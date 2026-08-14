//! Rust port of the float-screening hot path of the atlas certificate
//! search (`projective_local_axis_candidates` /
//! `projective_local_float_candidates`).  Every operation mirrors the
//! Python source ordering exactly so results are bit-identical: same
//! float evaluation order, Python banker's rounding, stable sorts,
//! first-minimum argmin, and correctly-rounded rational->f64 conversion
//! (matching `float(Fraction)`).  This code is a *screen*: it selects
//! certificate candidates whose exact rational audit happens elsewhere,
//! and the Lean checker re-verifies every emitted row regardless.

use pyo3::prelude::*;
use pyo3::types::{PyDict, PyList};
use std::collections::HashSet;
use std::sync::Mutex;

// ---------------------------------------------------------------- tables ---

struct Tables {
    vertices: Vec<[f64; 3]>,
    // exact vertex coordinates as numerators over one common denominator
    vq_num: Vec<[i128; 3]>,
    vq_den: i128,
    trunc_float: bool,
}

static TABLES: Mutex<Option<Tables>> = Mutex::new(None);

#[pyfunction]
fn install(vertices: Vec<[f64; 3]>, vq_num: Vec<[i128; 3]>, vq_den: i128,
           trunc_float: bool) {
    assert!(vq_den > 0);
    for row in &vq_num {
        for &n in row {
            // headroom check: mixed-edge numerators stay ≤ 2000*|n|,
            // and to_f64 shifting needs ≤ ~2^90 here.
            assert!(n.abs() < (1i128 << 80), "vertex numerator too large");
        }
    }
    *TABLES.lock().unwrap() = Some(Tables { vertices, vq_num, vq_den, trunc_float });
}

// ------------------------------------------------------------- small math ---

/// CPython 3.12+ builtin sum() float fast path: Neumaier compensated
/// summation (bltinmodule.c).  Bit-identical replication is required.
#[inline]
fn py_sum3(x0: f64, x1: f64, x2: f64) -> f64 {
    let mut result = 0.0f64;
    let mut comp = 0.0f64;
    for x in [x0, x1, x2] {
        let t = result + x;
        if result.abs() >= x.abs() {
            comp += (result - t) + x;
        } else {
            comp += (x - t) + result;
        }
        result = t;
    }
    result + comp
}

#[inline]
fn dot3(a: &[f64; 3], b: &[f64; 3]) -> f64 {
    // Python: sum(x*y for ...) — compensated since 3.12.
    py_sum3(a[0] * b[0], a[1] * b[1], a[2] * b[2])
}

#[inline]
fn cross3(a: &[f64; 3], b: &[f64; 3]) -> [f64; 3] {
    [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    ]
}

#[inline]
fn norm3(v: &[f64; 3]) -> f64 {
    dot3(v, v).sqrt()
}

/// Python round() on a non-negative float: round-half-to-even.
fn python_round_i64(x: f64) -> i64 {
    let floor = x.floor();
    let frac = x - floor;
    let f = floor as i64;
    if frac > 0.5 {
        f + 1
    } else if frac < 0.5 {
        f
    } else if f % 2 == 0 {
        f
    } else {
        f + 1
    }
}

// ------------------------------------------------- exact rational helpers ---

fn gcd128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    if a == 0 { 1 } else { a }
}

#[derive(Clone, Copy)]
struct Rat {
    num: i128,
    den: i128, // > 0
}

impl Rat {
    fn new(num: i128, den: i128) -> Rat {
        assert!(den != 0);
        let sign = if den < 0 { -1 } else { 1 };
        let g = gcd128(num, den);
        Rat { num: sign * num / g, den: sign * den / g }
    }
    fn sub(self, other: Rat) -> Rat {
        Rat::new(
            self.num
                .checked_mul(other.den)
                .and_then(|a| other.num.checked_mul(self.den)
                          .and_then(|b| a.checked_sub(b)))
                .expect("Rat::sub overflow"),
            self.den.checked_mul(other.den).expect("Rat::sub overflow"),
        )
    }
    fn add(self, other: Rat) -> Rat {
        Rat::new(
            self.num
                .checked_mul(other.den)
                .and_then(|a| other.num.checked_mul(self.den)
                          .and_then(|b| a.checked_add(b)))
                .expect("Rat::add overflow"),
            self.den.checked_mul(other.den).expect("Rat::add overflow"),
        )
    }
    fn mul(self, other: Rat) -> Rat {
        Rat::new(
            self.num.checked_mul(other.num).expect("Rat::mul overflow"),
            self.den.checked_mul(other.den).expect("Rat::mul overflow"),
        )
    }
    /// Correctly rounded conversion (round-half-to-even), matching
    /// CPython float(Fraction).  Values here are far from the subnormal
    /// and overflow ranges, so only the normal path is implemented.
    fn to_f64(self, trunc: bool) -> f64 {
        if self.num == 0 {
            return 0.0;
        }
        let neg = self.num < 0;
        let num0 = self.num.unsigned_abs();
        let den0 = self.den.unsigned_abs();
        let bits = |x: u128| (128 - x.leading_zeros()) as i32;
        // Scale so the integer quotient q = floor(num/den * 2^s) carries
        // 56 or 57 significant bits; value = (q + r/den) * 2^-s.
        let s = 56 - (bits(num0) - bits(den0));
        let (num, den) = if s >= 0 {
            assert!(bits(num0) + s <= 127, "to_f64 shift overflow");
            (num0 << s, den0)
        } else {
            assert!(bits(den0) + (-s) <= 127, "to_f64 shift overflow");
            (num0, den0 << (-s))
        };
        let q = num / den;
        let r = num % den;
        let qb = bits(q);
        debug_assert!((54..=57).contains(&qb));
        let extra = qb - 53;
        let half = 1u128 << (extra - 1);
        let low = q & ((1u128 << extra) - 1);
        let mut mant = q >> extra;
        let round_up = if trunc {
            false
        } else if low > half {
            true
        } else if low < half {
            false
        } else if r != 0 {
            true
        } else {
            mant & 1 == 1
        };
        let mut exp = -s + extra;
        if round_up {
            mant += 1;
            if bits(mant) > 53 {
                mant >>= 1;
                exp += 1;
            }
        }
        let value = (mant as f64) * (2f64).powi(exp);
        if neg { -value } else { value }
    }
}

// ------------------------------------------------------------ convex hull ---

/// Indices of the counterclockwise strict convex hull (Python port).
fn convex_hull(points: &[(f64, f64)]) -> Vec<usize> {
    let mut ordered: Vec<usize> = (0..points.len()).collect();
    // Python sorted(key=points[i]) — lexicographic (x, y), stable.
    ordered.sort_by(|&a, &b| {
        points[a]
            .partial_cmp(&points[b])
            .expect("NaN in hull points")
    });
    let half = |indices: &mut dyn Iterator<Item = usize>| -> Vec<usize> {
        let mut answer: Vec<usize> = Vec::new();
        for index in indices {
            while answer.len() >= 2 {
                let a = points[answer[answer.len() - 2]];
                let b = points[answer[answer.len() - 1]];
                let ab = (b.0 - a.0, b.1 - a.1);
                let bp = (points[index].0 - b.0, points[index].1 - b.1);
                if ab.0 * bp.1 - ab.1 * bp.0 > 1e-14 {
                    break;
                }
                answer.pop();
            }
            answer.push(index);
        }
        answer
    };
    let lower = half(&mut ordered.iter().copied());
    let upper = half(&mut ordered.iter().rev().copied());
    let mut result = lower[..lower.len() - 1].to_vec();
    result.extend_from_slice(&upper[..upper.len() - 1]);
    result
}

// -------------------------------------------------------------- contacts ---

#[derive(Clone)]
struct Contact {
    vertex: usize,
    lift: [f64; 3],
    direction_bound: f64,
    lambda: f64,
    edge_start: usize,
    edge_finish: usize,
    edge_start2: usize,
    edge_finish2: usize,
    mix: i64,
}

type ContactKey = (usize, usize, usize, usize, i64, usize);

impl Contact {
    fn key(&self) -> ContactKey {
        (self.edge_start, self.edge_finish, self.edge_start2,
         self.edge_finish2, self.mix, self.vertex)
    }
}

struct Candidate {
    contacts: [Contact; 3],
    weights: [f64; 3],
    normalized_a: [f64; 3],
    b: f64,
}

/// Port of projective_local_axis_candidates.
fn axis_candidates(
    tables: &Tables,
    view: &[f64; 3],
    cone_samples: usize,
    include_boundaries: bool,
    allow_zero_weights: bool,
) -> (Vec<usize>, Vec<Candidate>) {
    let vertices = &tables.vertices;
    let length = norm3(view);
    let unit_view = [view[0] / length, view[1] / length, view[2] / length];
    // min(range(3), key=abs) — first minimum wins
    let mut axis_index = 0usize;
    for i in 1..3 {
        if unit_view[i].abs() < unit_view[axis_index].abs() {
            axis_index = i;
        }
    }
    let mut axis = [0.0f64; 3];
    axis[axis_index] = 1.0;
    let mut first = cross3(&unit_view, &axis);
    let inv = 1.0 / norm3(&first);
    first = [inv * first[0], inv * first[1], inv * first[2]];
    let second = cross3(&unit_view, &first);
    let projected: Vec<(f64, f64)> = vertices
        .iter()
        .map(|v| (dot3(v, &first), dot3(v, &second)))
        .collect();
    let cycle = convex_hull(&projected);
    let n = cycle.len();
    let edges: Vec<[f64; 3]> = (0..n)
        .map(|position| {
            let start = cycle[position];
            let finish = cycle[(position + 1) % n];
            [
                vertices[finish][0] - vertices[start][0],
                vertices[finish][1] - vertices[start][1],
                vertices[finish][2] - vertices[start][2],
            ]
        })
        .collect();

    let mut contacts: Vec<Contact> = Vec::new();
    for position in 0..n {
        let vertex = cycle[position];
        let previous = cycle[(position + n - 1) % n];
        let following = cycle[(position + 1) % n];
        let before = edges[(position + n - 1) % n];
        let after = edges[position];
        let mut samples: Vec<f64> = (0..cone_samples)
            .map(|s| (s as f64 + 1.0) / (cone_samples as f64 + 1.0))
            .collect();
        if include_boundaries {
            let near = [0.0f64, 1.0 / 1000.0];
            let mut all: Vec<f64> = Vec::new();
            all.extend_from_slice(&near);
            all.extend_from_slice(&samples);
            all.extend(near.iter().map(|v| 1.0 - v));
            all.sort_by(|a, b| a.partial_cmp(b).unwrap());
            all.dedup();
            samples = all;
        }
        for &lam in &samples {
            let edge_combination = [
                lam * before[0] + (1.0 - lam) * after[0],
                lam * before[1] + (1.0 - lam) * after[1],
                lam * before[2] + (1.0 - lam) * after[2],
            ];
            let lift = cross3(&unit_view, &edge_combination);
            let direction_bound =
                lam * norm3(&before) + (1.0 - lam) * norm3(&after);
            contacts.push(Contact {
                vertex,
                lift,
                direction_bound,
                lambda: lam,
                edge_start: previous,
                edge_finish: vertex,
                edge_start2: vertex,
                edge_finish2: following,
                mix: python_round_i64(1000.0 * lam),
            });
        }
    }

    let mut candidates: Vec<Candidate> = Vec::new();
    let m = contacts.len();
    for i in 0..m {
        for j in (i + 1)..m {
            for k in (j + 1)..m {
                let selected = [&contacts[i], &contacts[j], &contacts[k]];
                let lifts = [selected[0].lift, selected[1].lift,
                             selected[2].lift];
                let mut weights = [
                    dot3(&unit_view, &cross3(&lifts[1], &lifts[2])),
                    dot3(&unit_view, &cross3(&lifts[2], &lifts[0])),
                    dot3(&unit_view, &cross3(&lifts[0], &lifts[1])),
                ];
                if weights.iter().all(|&w| w <= 1e-12) {
                    for w in weights.iter_mut() {
                        *w = -*w;
                    }
                }
                if allow_zero_weights {
                    let wmin = weights.iter().cloned().fold(f64::INFINITY,
                                                            f64::min);
                    let wmax = weights.iter().cloned().fold(
                        f64::NEG_INFINITY, f64::max);
                    if wmin < -1e-10 || wmax <= 1e-10 {
                        continue;
                    }
                    for w in weights.iter_mut() {
                        if w.abs() <= 1e-10 {
                            *w = 0.0;
                        }
                    }
                } else if !weights.iter().all(|&w| w > 1e-10) {
                    continue;
                }
                let mut a = [0.0f64; 3];
                let mut b = 0.0f64;
                for t in 0..3 {
                    let contact = selected[t];
                    let term = cross3(&vertices[contact.vertex],
                                      &lifts[t]);
                    // Python: a = [left + weight*right ...]
                    a = [
                        a[0] + weights[t] * term[0],
                        a[1] + weights[t] * term[1],
                        a[2] + weights[t] * term[2],
                    ];
                    b += weights[t] * contact.direction_bound;
                }
                candidates.push(Candidate {
                    contacts: [selected[0].clone(), selected[1].clone(),
                               selected[2].clone()],
                    weights,
                    normalized_a: [a[0] / b, a[1] / b, a[2] / b],
                    b,
                });
            }
        }
    }
    (cycle, candidates)
}

/// Port of projective_mixed_edge_q followed by float(): with every vertex
/// coordinate over the common denominator D, the edge component is
/// (m*(s-f) + (1000-m)*(s2-f2)) / (1000*D) exactly.
fn mixed_edge_float(tables: &Tables, c: &Contact) -> [f64; 3] {
    let m = c.mix as i128;
    let mut out = [0.0f64; 3];
    for i in 0..3 {
        let first = tables.vq_num[c.edge_start][i]
            - tables.vq_num[c.edge_finish][i];
        let second = tables.vq_num[c.edge_start2][i]
            - tables.vq_num[c.edge_finish2][i];
        let num = m.checked_mul(first)
            .and_then(|a| (1000 - m).checked_mul(second)
                      .and_then(|b| a.checked_add(b)))
            .expect("mixed_edge overflow");
        let den = tables.vq_den.checked_mul(1000)
            .expect("mixed_edge overflow");
        out[i] = Rat::new(num, den).to_f64(tables.trunc_float);
    }
    out
}

fn contact_exact_tie(c: &Contact, target: usize) -> bool {
    if target == c.vertex {
        return true;
    }
    if c.mix == 1000 && c.vertex == c.edge_finish && target == c.edge_start {
        return true;
    }
    c.mix == 0 && c.vertex == c.edge_start2 && target == c.edge_finish2
}

struct Feasible {
    contacts: [Contact; 3],
    normalized_a: [f64; 3],
    strict_slack: f64,
}

/// Port of projective_local_float_candidates.
fn local_float_candidates(
    tables: &Tables,
    triangle: &[[f64; 3]; 3],
    cone_samples: usize,
    include_boundaries: bool,
    include_corner_cycles: bool,
    screen_support_error: f64,
) -> Vec<Feasible> {
    let vertices = &tables.vertices;
    let centroid = [
        py_sum3(triangle[0][0], triangle[1][0], triangle[2][0]) / 3.0,
        py_sum3(triangle[0][1], triangle[1][1], triangle[2][1]) / 3.0,
        py_sum3(triangle[0][2], triangle[1][2], triangle[2][2]) / 3.0,
    ];
    let mut sample_views: Vec<[f64; 3]> = vec![centroid];
    if include_corner_cycles {
        sample_views.extend_from_slice(triangle);
    }
    let mut candidates: Vec<Candidate> = Vec::new();
    let mut seen: HashSet<[ContactKey; 3]> = HashSet::new();
    for sample_view in &sample_views {
        let (_, sample_candidates) =
            axis_candidates(tables, sample_view, cone_samples,
                            include_boundaries, false);
        for candidate in sample_candidates {
            let key = [
                candidate.contacts[0].key(),
                candidate.contacts[1].key(),
                candidate.contacts[2].key(),
            ];
            if seen.insert(key) {
                candidates.push(candidate);
            }
        }
    }
    // support cache
    use std::collections::HashMap;
    struct Support {
        edge: [f64; 3],
        selected: usize,
        strict_slack: f64,
        support_ok: bool,
    }
    let mut support_cache: HashMap<ContactKey, Support> = HashMap::new();
    let mut feasible: Vec<Feasible> = Vec::new();
    for candidate in &candidates {
        let mut contacts = candidate.contacts.clone();
        {
            // populate cache entries
            for contact in &contacts {
                let key = contact.key();
                if support_cache.contains_key(&key) {
                    continue;
                }
                let edge = mixed_edge_float(tables, contact);
                let selected = contact.vertex;
                let mut strict_slack = f64::INFINITY;
                let mut support_ok = true;
                for (k, vertex) in vertices.iter().enumerate() {
                    if contact_exact_tie(contact, k) {
                        continue;
                    }
                    let delta = [
                        vertex[0] - vertices[selected][0],
                        vertex[1] - vertices[selected][1],
                        vertex[2] - vertices[selected][2],
                    ];
                    let coefficient = cross3(&edge, &delta);
                    // max over corners, first-max semantics irrelevant for
                    // value; Python max of generator
                    let mut mx = dot3(&triangle[0], &coefficient);
                    for corner in &triangle[1..] {
                        let v = dot3(corner, &coefficient);
                        if v > mx {
                            mx = v;
                        }
                    }
                    let upper = mx + screen_support_error;
                    let neg = -upper;
                    if neg < strict_slack {
                        strict_slack = neg;
                    }
                    if upper > 0.0 {
                        support_ok = false;
                        break;
                    }
                }
                support_cache.insert(key, Support {
                    edge, selected, strict_slack, support_ok,
                });
            }
        }
        let data: Vec<&Support> = contacts
            .iter()
            .map(|c| support_cache.get(&c.key()).unwrap())
            .collect();
        let mut edges = [data[0].edge, data[1].edge, data[2].edge];
        let mut supports = [data[0].selected, data[1].selected,
                            data[2].selected];
        let mut slacks = [data[0].strict_slack, data[1].strict_slack,
                          data[2].strict_slack];
        let oks = [data[0].support_ok, data[1].support_ok,
                   data[2].support_ok];
        let mut oks = oks;
        let probe = [
            dot3(&triangle[0], &cross3(&edges[1], &edges[2])),
            dot3(&triangle[0], &cross3(&edges[2], &edges[0])),
            dot3(&triangle[0], &cross3(&edges[0], &edges[1])),
        ];
        let probe_max = probe.iter().cloned().fold(f64::NEG_INFINITY,
                                                   f64::max);
        if probe_max < 0.0 {
            contacts.swap(1, 2);
            edges.swap(1, 2);
            supports.swap(1, 2);
            slacks.swap(1, 2);
            oks.swap(1, 2);
        }
        let weight_coefficients = [
            cross3(&edges[1], &edges[2]),
            cross3(&edges[2], &edges[0]),
            cross3(&edges[0], &edges[1]),
        ];
        let weights_at: Vec<[f64; 3]> = weight_coefficients
            .iter()
            .map(|coefficient| {
                [
                    dot3(&triangle[0], coefficient),
                    dot3(&triangle[1], coefficient),
                    dot3(&triangle[2], coefficient),
                ]
            })
            .collect();
        let weight_lower: Vec<f64> = weights_at
            .iter()
            .map(|values| {
                values.iter().cloned().fold(f64::INFINITY, f64::min)
                    - screen_support_error
            })
            .collect();
        let wl_min = weight_lower.iter().cloned().fold(f64::INFINITY,
                                                       f64::min);
        let wl_max = weight_lower.iter().cloned().fold(f64::NEG_INFINITY,
                                                       f64::max);
        if wl_min < 0.0 || wl_max <= 0.0 {
            continue;
        }
        let strict_slack = slacks.iter().cloned().fold(f64::INFINITY,
                                                       f64::min);
        if !(oks[0] && oks[1] && oks[2]) {
            continue;
        }
        let n_ = centroid;
        let weights = [
            dot3(&n_, &weight_coefficients[0]),
            dot3(&n_, &weight_coefficients[1]),
            dot3(&n_, &weight_coefficients[2]),
        ];
        // B = 2*sum(max(values)+err for values in weights_at); sum starts 0
        let terms: Vec<f64> = weights_at
            .iter()
            .map(|values| values.iter().cloned()
                 .fold(f64::NEG_INFINITY, f64::max) + screen_support_error)
            .collect();
        let b = 2.0 * py_sum3(terms[0], terms[1], terms[2]);
        let mut variation = [0.0f64; 3];
        for t in 0..3 {
            let lift = cross3(&n_, &edges[t]);
            let term = cross3(&vertices[supports[t]], &lift);
            variation = [
                variation[0] + weights[t] * term[0],
                variation[1] + weights[t] * term[1],
                variation[2] + weights[t] * term[2],
            ];
        }
        feasible.push(Feasible {
            contacts,
            normalized_a: [variation[0] / b, variation[1] / b,
                           variation[2] / b],
            strict_slack,
        });
    }
    feasible
}

// ------------------------------------------------------------ python glue ---

fn contact_to_py<'py>(py: Python<'py>, c: &Contact)
                      -> PyResult<Bound<'py, PyDict>> {
    let d = PyDict::new(py);
    d.set_item("vertex", c.vertex)?;
    d.set_item("lift", (c.lift[0], c.lift[1], c.lift[2]))?;
    d.set_item("direction_bound", c.direction_bound)?;
    d.set_item("lambda", c.lambda)?;
    d.set_item("edge_start", c.edge_start)?;
    d.set_item("edge_finish", c.edge_finish)?;
    d.set_item("edge_start2", c.edge_start2)?;
    d.set_item("edge_finish2", c.edge_finish2)?;
    d.set_item("mix", c.mix)?;
    Ok(d)
}

#[pyfunction]
#[pyo3(signature = (triangle, cone_samples=4, include_boundaries=false,
                    include_corner_cycles=false, screen_support_error=5e-15))]
fn projective_local_float_candidates<'py>(
    py: Python<'py>,
    triangle: [[f64; 3]; 3],
    cone_samples: usize,
    include_boundaries: bool,
    include_corner_cycles: bool,
    screen_support_error: f64,
) -> PyResult<Bound<'py, PyList>> {
    let guard = TABLES.lock().unwrap();
    let tables = guard
        .as_ref()
        .ok_or_else(|| pyo3::exceptions::PyRuntimeError::new_err(
            "nopert_kernel.install() not called"))?;
    let feasible = py.allow_threads(|| {
        local_float_candidates(tables, &triangle, cone_samples,
                               include_boundaries, include_corner_cycles,
                               screen_support_error)
    });
    let out = PyList::empty(py);
    for f in &feasible {
        let d = PyDict::new(py);
        let contacts = PyList::empty(py);
        for c in &f.contacts {
            contacts.append(contact_to_py(py, c)?)?;
        }
        d.set_item("contacts", contacts)?;
        d.set_item("normalized_a", (f.normalized_a[0], f.normalized_a[1],
                                    f.normalized_a[2]))?;
        d.set_item("strict_slack", f.strict_slack)?;
        out.append(d)?;
    }
    Ok(out)
}

#[pyfunction]
#[pyo3(signature = (view, cone_samples=1, include_boundaries=false,
                    allow_zero_weights=false))]
fn projective_local_axis_candidates<'py>(
    py: Python<'py>,
    view: [f64; 3],
    cone_samples: usize,
    include_boundaries: bool,
    allow_zero_weights: bool,
) -> PyResult<(Vec<usize>, Bound<'py, PyList>)> {
    let guard = TABLES.lock().unwrap();
    let tables = guard
        .as_ref()
        .ok_or_else(|| pyo3::exceptions::PyRuntimeError::new_err(
            "nopert_kernel.install() not called"))?;
    let (cycle, candidates) = py.allow_threads(|| {
        axis_candidates(tables, &view, cone_samples, include_boundaries,
                        allow_zero_weights)
    });
    let out = PyList::empty(py);
    for cand in &candidates {
        let d = PyDict::new(py);
        let contacts = PyList::empty(py);
        for c in &cand.contacts {
            contacts.append(contact_to_py(py, c)?)?;
        }
        d.set_item("contacts", contacts)?;
        d.set_item("weights", (cand.weights[0], cand.weights[1],
                               cand.weights[2]))?;
        d.set_item("normalized_a", (cand.normalized_a[0],
                                    cand.normalized_a[1],
                                    cand.normalized_a[2]))?;
        d.set_item("B", cand.b)?;
        out.append(d)?;
    }
    Ok((cycle, out))
}

#[pyfunction]
fn debug_pipeline<'py>(
    py: Python<'py>,
    triangle: [[f64; 3]; 3],
    keys: [(usize, usize, usize, usize, i64, usize); 3],
    screen_support_error: f64,
) -> PyResult<Bound<'py, PyDict>> {
    let guard = TABLES.lock().unwrap();
    let tables = guard.as_ref().expect("install first");
    let vertices = &tables.vertices;
    let centroid = [
        py_sum3(triangle[0][0], triangle[1][0], triangle[2][0]) / 3.0,
        py_sum3(triangle[0][1], triangle[1][1], triangle[2][1]) / 3.0,
        py_sum3(triangle[0][2], triangle[1][2], triangle[2][2]) / 3.0,
    ];
    let contact = |k: (usize, usize, usize, usize, i64, usize)| Contact {
        vertex: k.5, lift: [0.0; 3], direction_bound: 0.0, lambda: 0.0,
        edge_start: k.0, edge_finish: k.1, edge_start2: k.2,
        edge_finish2: k.3, mix: k.4,
    };
    let contacts = [contact(keys[0]), contact(keys[1]), contact(keys[2])];
    let edges = [
        mixed_edge_float(tables, &contacts[0]),
        mixed_edge_float(tables, &contacts[1]),
        mixed_edge_float(tables, &contacts[2]),
    ];
    let supports = [contacts[0].vertex, contacts[1].vertex,
                    contacts[2].vertex];
    let weight_coefficients = [
        cross3(&edges[1], &edges[2]),
        cross3(&edges[2], &edges[0]),
        cross3(&edges[0], &edges[1]),
    ];
    let weights_at: Vec<[f64; 3]> = weight_coefficients.iter()
        .map(|c| [dot3(&triangle[0], c), dot3(&triangle[1], c),
                  dot3(&triangle[2], c)]).collect();
    let terms: Vec<f64> = weights_at
        .iter()
        .map(|values| values.iter().cloned()
             .fold(f64::NEG_INFINITY, f64::max) + screen_support_error)
        .collect();
    let b = 2.0 * py_sum3(terms[0], terms[1], terms[2]);
    let weights = [
        dot3(&centroid, &weight_coefficients[0]),
        dot3(&centroid, &weight_coefficients[1]),
        dot3(&centroid, &weight_coefficients[2]),
    ];
    let mut variation = [0.0f64; 3];
    for t in 0..3 {
        let lift = cross3(&centroid, &edges[t]);
        let term = cross3(&vertices[supports[t]], &lift);
        variation = [
            variation[0] + weights[t] * term[0],
            variation[1] + weights[t] * term[1],
            variation[2] + weights[t] * term[2],
        ];
    }
    let d = PyDict::new(py);
    d.set_item("centroid", centroid.to_vec())?;
    d.set_item("edges", edges.iter().map(|e| e.to_vec()).collect::<Vec<_>>())?;
    d.set_item("wc", weight_coefficients.iter().map(|e| e.to_vec())
               .collect::<Vec<_>>())?;
    d.set_item("weights_at", weights_at.iter().map(|e| e.to_vec())
               .collect::<Vec<_>>())?;
    d.set_item("B", b)?;
    d.set_item("weights", weights.to_vec())?;
    d.set_item("variation", variation.to_vec())?;
    d.set_item("normalized_a", [variation[0]/b, variation[1]/b,
                                variation[2]/b].to_vec())?;
    Ok(d)
}

#[pyfunction]
fn debug_mixed_edge(edge_start: usize, edge_finish: usize,
                    edge_start2: usize, edge_finish2: usize,
                    mix: i64, vertex: usize) -> [f64; 3] {
    let guard = TABLES.lock().unwrap();
    let tables = guard.as_ref().expect("install first");
    let c = Contact {
        vertex, lift: [0.0; 3], direction_bound: 0.0, lambda: 0.0,
        edge_start, edge_finish, edge_start2, edge_finish2, mix,
    };
    mixed_edge_float(tables, &c)
}

#[pymodule]
fn nopert_kernel(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(debug_mixed_edge, m)?)?;
    m.add_function(wrap_pyfunction!(debug_pipeline, m)?)?;
    m.add_function(wrap_pyfunction!(weighted_defect_upper_float, m)?)?;
    m.add_function(wrap_pyfunction!(mixed_candidate_column, m)?)?;
    m.add_function(wrap_pyfunction!(float_screen_rank, m)?)?;
    m.add_function(wrap_pyfunction!(simplex_bernstein_controls, m)?)?;
    m.add_function(wrap_pyfunction!(install, m)?)?;
    m.add_function(wrap_pyfunction!(projective_local_float_candidates, m)?)?;
    m.add_function(wrap_pyfunction!(projective_local_axis_candidates, m)?)?;
    Ok(())
}

// ================================================================ cluster 2
// Ports of the global mixed-candidate float machinery.  These mirror the
// NUMPY code paths (plain left-fold arithmetic, elementwise ops) — NOT the
// _py fallbacks and NOT compensated sums, because the live engine runs the
// numpy branch.

use numpy::{PyReadonlyArray3, PyArrayMethods};

/// weighted_defect_upper_float (numpy path): plain folds throughout.
fn weighted_defect_upper(
    tables: &Tables,
    triangle: &[[f64; 3]; 3],
    contacts: &[Contact; 3],
    error: f64,
) -> f64 {
    let vertices = &tables.vertices;
    let edges = [
        mixed_edge_float(tables, &contacts[0]),
        mixed_edge_float(tables, &contacts[1]),
        mixed_edge_float(tables, &contacts[2]),
    ];
    let weight_coefficients = [
        cross3(&edges[1], &edges[2]),
        cross3(&edges[2], &edges[0]),
        cross3(&edges[0], &edges[1]),
    ];
    let mut total = 0.0f64;
    for i in 0..3 {
        let selected = contacts[i].vertex;
        let wc = weight_coefficients[i];
        // tri[:,0]*wc0 + tri[:,1]*wc1 + tri[:,2]*wc2 + error  (plain fold)
        let weight_values: [f64; 3] = [
            triangle[0][0] * wc[0] + triangle[0][1] * wc[1]
                + triangle[0][2] * wc[2] + error,
            triangle[1][0] * wc[0] + triangle[1][1] * wc[1]
                + triangle[1][2] * wc[2] + error,
            triangle[2][0] * wc[0] + triangle[2][1] * wc[1]
                + triangle[2][2] * wc[2] + error,
        ];
        let (e0, e1, e2) = (edges[i][0], edges[i][1], edges[i][2]);
        let sel = vertices[selected];
        let mut cmax = f64::NEG_INFINITY;
        for (k, vertex) in vertices.iter().enumerate() {
            let delta = [vertex[0] - sel[0], vertex[1] - sel[1],
                         vertex[2] - sel[2]];
            let sc = [
                e1 * delta[2] - e2 * delta[1],
                e2 * delta[0] - e0 * delta[2],
                e0 * delta[1] - e1 * delta[0],
            ];
            let sv: [f64; 3] = [
                triangle[0][0] * sc[0] + triangle[0][1] * sc[1]
                    + triangle[0][2] * sc[2] + error,
                triangle[1][0] * sc[0] + triangle[1][1] * sc[1]
                    + triangle[1][2] * sc[2] + error,
                triangle[2][0] * sc[0] + triangle[2][1] * sc[1]
                    + triangle[2][2] * sc[2] + error,
            ];
            if k == selected {
                // numpy zeroes this column after the fact
                continue;
            }
            for a in 0..3 {
                for b in 0..3 {
                    let control = (weight_values[a] * sv[b]
                                   + weight_values[b] * sv[a]) / 2.0;
                    if control > cmax {
                        cmax = control;
                    }
                }
            }
        }
        // controls[:, :, selected] = 0.0 then .max(): the zeroed column
        // participates in the max, so floor at 0.0 exactly like numpy.
        if 0.0 > cmax {
            cmax = 0.0;
        }
        total += if 0.0 > cmax { 0.0 } else { cmax }.max(0.0);
    }
    total
}

/// polynomial_at_view (numpy path inside simplex controls).
fn polynomial_at_view(
    stacks: &[&[f64]; 3],      // each (V,3,10) row-major
    weight_coefficients: &[[f64; 3]; 3],
    inner_indices: &[usize; 3],
    multiplier: f64,
    view: &[f64; 3],
) -> [f64; 10] {
    let mut total = [0.0f64; 10];
    for i in 0..3 {
        let comp = &stacks[i][inner_indices[i] * 30..inner_indices[i] * 30 + 30];
        let wc = weight_coefficients[i];
        let weight = view[0] * wc[0] + view[1] * wc[1] + view[2] * wc[2];
        for t in 0..10 {
            let scalar = view[0] * comp[t] + view[1] * comp[10 + t]
                + view[2] * comp[20 + t];
            total[t] += weight * scalar;
        }
    }
    total[0] -= 3.0 * multiplier;
    for index in [4, 7, 9] {
        total[index] += multiplier;
    }
    total
}

/// _bernstein_controls_27_np for P polynomials: returns per-poly [f64;27].
fn bernstein_controls_27(
    polys: &[[f64; 10]],
    centers: &[f64; 3],
    radii: &[f64; 3],
) -> Vec<[f64; 27]> {
    let (lx, ly, lz) = (centers[0] - radii[0], centers[1] - radii[1],
                        centers[2] - radii[2]);
    let (wx, wy, wz) = (2.0 * radii[0], 2.0 * radii[1], 2.0 * radii[2]);
    polys
        .iter()
        .map(|c| {
            let a0 = c[0] + c[1] * lx + c[2] * ly + c[3] * lz
                + c[4] * lx * lx + c[5] * lx * ly + c[6] * lx * lz
                + c[7] * ly * ly + c[8] * ly * lz + c[9] * lz * lz;
            let ax = wx * (c[1] + 2.0 * c[4] * lx + c[5] * ly + c[6] * lz);
            let ay = wy * (c[2] + c[5] * lx + 2.0 * c[7] * ly + c[8] * lz);
            let az = wz * (c[3] + c[6] * lx + c[8] * ly + 2.0 * c[9] * lz);
            let (axx, ayy, azz) = (c[4] * wx * wx, c[7] * wy * wy,
                                   c[9] * wz * wz);
            let (axy, axz, ayz) = (c[5] * wx * wy, c[6] * wx * wz,
                                   c[8] * wy * wz);
            let mut out = [0.0f64; 27];
            let mut idx = 0;
            for i in 0..3usize {
                for j in 0..3usize {
                    for k in 0..3usize {
                        let (fi, fj, fk) = (i as f64, j as f64, k as f64);
                        out[idx] = a0 + (fi / 2.0) * ax + (fj / 2.0) * ay
                            + (fk / 2.0) * az
                            + if i == 2 { axx } else { 0.0 }
                            + if j == 2 { ayy } else { 0.0 }
                            + if k == 2 { azz } else { 0.0 }
                            + (fi * fj / 4.0) * axy
                            + (fi * fk / 4.0) * axz
                            + (fj * fk / 4.0) * ayz;
                        idx += 1;
                    }
                }
            }
            out
        })
        .collect()
}

/// simplex_bernstein_controls_float (numpy path): 27x6 flattened.
fn simplex_controls(
    tables: &Tables,
    stacks: &[&[f64]; 3],
    triangle: &[[f64; 3]; 3],
    contacts: &[Contact; 3],
    centers: &[f64; 3],
    radii: &[f64; 3],
    inner_indices: &[usize; 3],
    multiplier: f64,
) -> Vec<f64> {
    let edges = [
        mixed_edge_float(tables, &contacts[0]),
        mixed_edge_float(tables, &contacts[1]),
        mixed_edge_float(tables, &contacts[2]),
    ];
    let weight_coefficients = [
        cross3(&edges[1], &edges[2]),
        cross3(&edges[2], &edges[0]),
        cross3(&edges[0], &edges[1]),
    ];
    let mut views: Vec<[f64; 3]> = triangle.to_vec();
    for i in 0..3 {
        for j in (i + 1)..3 {
            views.push([
                (triangle[i][0] + triangle[j][0]) / 2.0,
                (triangle[i][1] + triangle[j][1]) / 2.0,
                (triangle[i][2] + triangle[j][2]) / 2.0,
            ]);
        }
    }
    let polys: Vec<[f64; 10]> = views
        .iter()
        .map(|v| polynomial_at_view(stacks, &weight_coefficients,
                                    inner_indices, multiplier, v))
        .collect();
    let ctrl = bernstein_controls_27(&polys, centers, radii);
    let mut out = Vec::with_capacity(27 * 6);
    for k in 0..27 {
        out.push(ctrl[0][k]);
        out.push(ctrl[1][k]);
        out.push(ctrl[2][k]);
        out.push(2.0 * ctrl[3][k] - (ctrl[0][k] + ctrl[1][k]) / 2.0);
        out.push(2.0 * ctrl[4][k] - (ctrl[0][k] + ctrl[2][k]) / 2.0);
        out.push(2.0 * ctrl[5][k] - (ctrl[1][k] + ctrl[2][k]) / 2.0);
    }
    out
}

fn contact_from_key(k: (usize, usize, usize, usize, i64, usize)) -> Contact {
    Contact {
        vertex: k.5, lift: [0.0; 3], direction_bound: 0.0, lambda: 0.0,
        edge_start: k.0, edge_finish: k.1, edge_start2: k.2,
        edge_finish2: k.3, mix: k.4,
    }
}

#[pyfunction]
fn weighted_defect_upper_float(
    triangle: [[f64; 3]; 3],
    keys: [(usize, usize, usize, usize, i64, usize); 3],
    error: f64,
) -> f64 {
    let guard = TABLES.lock().unwrap();
    let tables = guard.as_ref().expect("install first");
    let contacts = [contact_from_key(keys[0]), contact_from_key(keys[1]),
                    contact_from_key(keys[2])];
    weighted_defect_upper(tables, &triangle, &contacts, error)
}

#[pyfunction]
#[allow(clippy::too_many_arguments)]
fn mixed_candidate_column<'py>(
    py: Python<'py>,
    stack0: PyReadonlyArray3<'py, f64>,
    stack1: PyReadonlyArray3<'py, f64>,
    stack2: PyReadonlyArray3<'py, f64>,
    keys: [(usize, usize, usize, usize, i64, usize); 3],
    triangle: [[f64; 3]; 3],
    centers: [f64; 3],
    radii: [f64; 3],
    error: f64,
    kappa: f64,
) -> PyResult<Option<(Vec<usize>, Vec<f64>)>> {
    let guard = TABLES.lock().unwrap();
    let tables = guard.as_ref().expect("install first");
    let s0 = stack0.as_slice()?;
    let s1 = stack1.as_slice()?;
    let s2 = stack2.as_slice()?;
    let stacks: [&[f64]; 3] = [s0, s1, s2];
    let contacts = [contact_from_key(keys[0]), contact_from_key(keys[1]),
                    contact_from_key(keys[2])];
    let result = py.allow_threads(|| {
        let vcount = tables.vertices.len();
        // view_center: Python sum() over corners -> Neumaier, then /3
        let view_center = [
            py_sum3(triangle[0][0], triangle[1][0], triangle[2][0]) / 3.0,
            py_sum3(triangle[0][1], triangle[1][1], triangle[2][1]) / 3.0,
            py_sum3(triangle[0][2], triangle[1][2], triangle[2][2]) / 3.0,
        ];
        let edges = [
            mixed_edge_float(tables, &contacts[0]),
            mixed_edge_float(tables, &contacts[1]),
            mixed_edge_float(tables, &contacts[2]),
        ];
        let weight_coefficients = [
            cross3(&edges[1], &edges[2]),
            cross3(&edges[2], &edges[0]),
            cross3(&edges[0], &edges[1]),
        ];
        // weight_lower via compensated dot3 (Python-level min/dot3 code)
        let mut weight_lower = [0.0f64; 3];
        for (i, wc) in weight_coefficients.iter().enumerate() {
            let mut mn = f64::INFINITY;
            for corner in triangle.iter() {
                let v = dot3(corner, wc);
                if v < mn {
                    mn = v;
                }
            }
            weight_lower[i] = mn - error;
        }
        let wl_min = weight_lower.iter().cloned().fold(f64::INFINITY,
                                                       f64::min);
        let wl_max = weight_lower.iter().cloned().fold(f64::NEG_INFINITY,
                                                       f64::max);
        if wl_min < 0.0 || wl_max <= 0.0 {
            return None;
        }
        // inner argmax per contact (numpy path: plain elementwise)
        let (x, y, z) = (centers[0], centers[1], centers[2]);
        let mut inner_indices = [0usize; 3];
        for i in 0..3 {
            let stack = stacks[i];
            let mut best_val = f64::NEG_INFINITY;
            let mut best_idx = 0usize;
            for inner in 0..vcount {
                let mut vals = [0.0f64; 3];
                for c in 0..3 {
                    let a = &stack[inner * 30 + c * 10..inner * 30 + c * 10 + 10];
                    vals[c] = a[0] + a[1] * x + a[2] * y + a[3] * z
                        + a[4] * x * x + a[5] * x * y + a[6] * x * z
                        + a[7] * y * y + a[8] * y * z + a[9] * z * z;
                }
                let value = view_center[0] * vals[0]
                    + view_center[1] * vals[1] + view_center[2] * vals[2];
                if value > best_val {
                    best_val = value;
                    best_idx = inner;
                }
            }
            inner_indices[i] = best_idx;
        }
        let controls = simplex_controls(tables, &stacks, &triangle,
                                        &contacts, &centers, &radii,
                                        &inner_indices, 0.0);
        // d_bound: 1 + Python sum() of three squares (Neumaier)
        let endpoint_abs = [
            (centers[0] - radii[0]).abs().max((centers[0] + radii[0]).abs()),
            (centers[1] - radii[1]).abs().max((centers[1] + radii[1]).abs()),
            (centers[2] - radii[2]).abs().max((centers[2] + radii[2]).abs()),
        ];
        let d_bound = 1.0 + py_sum3(endpoint_abs[0] * endpoint_abs[0],
                                    endpoint_abs[1] * endpoint_abs[1],
                                    endpoint_abs[2] * endpoint_abs[2]);
        let defect = weighted_defect_upper(tables, &triangle, &contacts,
                                           error);
        let penalty = d_bound * defect + 300.0 * d_bound * kappa;
        let adjusted: Vec<f64> =
            controls.iter().map(|v| v - penalty).collect();
        Some((inner_indices.to_vec(), adjusted))
    });
    Ok(result)
}

// ================================================================ cluster 3
// float_screen ranking: center_data reward search + candidate scoring.
// Mirrors atlas_projective_global_float_screen lines 1449-1501: Python-level
// code, so dot3/score sums are compensated (py_sum3), sorts are stable.

const ATLAS_CHART_SIGNS_F: [[f64; 3]; 4] = [
    [1.0, 1.0, 1.0],
    [1.0, -1.0, -1.0],
    [-1.0, 1.0, -1.0],
    [-1.0, -1.0, 1.0],
];

struct CenterData {
    value: f64,
    inner: usize,
    edge: [f64; 3],
}

fn center_data_compute(
    tables: &Tables,
    chart: usize,
    contact: &Contact,
    view_center: &[f64; 3],
    numerator0: &[[f64; 3]; 3],
    denom0: f64,
) -> CenterData {
    let signs = ATLAS_CHART_SIGNS_F[chart];
    let edge = mixed_edge_float(tables, contact);
    let outer = tables.vertices[contact.vertex];
    let mut best_value = f64::NEG_INFINITY;
    let mut best_inner = 0usize;
    let mut first = true;
    for (inner, vertex) in tables.vertices.iter().enumerate() {
        let mut displacement = [0.0f64; 3];
        for c in 0..3 {
            // Python: float(sign)*sum(num0[c][j]*vertex[j] for j) - denom0*outer[c]
            let s = py_sum3(numerator0[c][0] * vertex[0],
                            numerator0[c][1] * vertex[1],
                            numerator0[c][2] * vertex[2]);
            displacement[c] = signs[c] * s - denom0 * outer[c];
        }
        let value = dot3(view_center, &cross3(&edge, &displacement));
        if first || value > best_value {
            best_value = value;
            best_inner = inner;
            first = false;
        }
    }
    CenterData { value: best_value, inner: best_inner, edge }
}

/// Rank candidates as in float_screen; returns (selected candidate indices,
/// per-candidate contact inners for the selected ones).
#[pyfunction]
#[allow(clippy::too_many_arguments)]
fn float_screen_rank(
    py: Python<'_>,
    chart: usize,
    triangle: [[f64; 3]; 3],
    candidates: Vec<[((usize, usize, usize, usize, i64, usize), f64); 3]>,
    relative_center: [f64; 3],
    d_bound: f64,
    candidate_limit: usize,
    allow_support_defect: bool,
) -> PyResult<(Vec<usize>, Vec<[usize; 3]>)> {
    let guard = TABLES.lock().unwrap();
    let tables = guard.as_ref().expect("install first");
    let out = py.allow_threads(|| {
        let view_center = [
            py_sum3(triangle[0][0], triangle[1][0], triangle[2][0]) / 3.0,
            py_sum3(triangle[0][1], triangle[1][1], triangle[2][1]) / 3.0,
            py_sum3(triangle[0][2], triangle[1][2], triangle[2][2]) / 3.0,
        ];
        let (x0, y0, z0) = (relative_center[0], relative_center[1],
                            relative_center[2]);
        let numerator0 = [
            [1.0 + x0 * x0 - y0 * y0 - z0 * z0, 2.0 * (x0 * y0 - z0),
             2.0 * (x0 * z0 + y0)],
            [2.0 * (x0 * y0 + z0), 1.0 - x0 * x0 + y0 * y0 - z0 * z0,
             2.0 * (y0 * z0 - x0)],
            [2.0 * (x0 * z0 - y0), 2.0 * (y0 * z0 + x0),
             1.0 - x0 * x0 - y0 * y0 + z0 * z0],
        ];
        let denom0 = 1.0 + x0 * x0 + y0 * y0 + z0 * z0;
        use std::collections::HashMap;
        let mut cache: HashMap<ContactKey, CenterData> = HashMap::new();
        let mut fetch = |key: (usize, usize, usize, usize, i64, usize)|
                        -> (f64, usize, [f64; 3]) {
            let entry = cache.entry(key).or_insert_with(|| {
                center_data_compute(tables, chart, &contact_from_key(key),
                                    &view_center, &numerator0, denom0)
            });
            (entry.value, entry.inner, entry.edge)
        };
        // score every candidate
        let mut scored: Vec<(f64, usize, bool, [usize; 3])> =
            Vec::with_capacity(candidates.len());
        for (idx, cand) in candidates.iter().enumerate() {
            let d0 = fetch(cand[0].0);
            let d1 = fetch(cand[1].0);
            let d2 = fetch(cand[2].0);
            let edges = [d0.2, d1.2, d2.2];
            let weights = [
                dot3(&view_center, &cross3(&edges[1], &edges[2])),
                dot3(&view_center, &cross3(&edges[2], &edges[0])),
                dot3(&view_center, &cross3(&edges[0], &edges[1])),
            ];
            let values = [d0.0, d1.0, d2.0];
            let mut score = py_sum3(weights[0] * values[0],
                                    weights[1] * values[1],
                                    weights[2] * values[2]);
            let defects = [cand[0].1, cand[1].1, cand[2].1];
            score -= d_bound
                * py_sum3(weights[0].max(0.0) * defects[0],
                          weights[1].max(0.0) * defects[1],
                          weights[2].max(0.0) * defects[2]);
            let strict = defects.iter().all(|&d| d == 0.0);
            scored.push((score, idx, strict, [d0.1, d1.1, d2.1]));
        }
        // Python: ranked.sort(key=score, reverse=True), stable.
        scored.sort_by(|a, b| b.0.partial_cmp(&a.0).unwrap());
        let selected: Vec<&(f64, usize, bool, [usize; 3])> =
            if allow_support_defect {
                let strict: Vec<_> = scored.iter().filter(|s| s.2)
                    .take(candidate_limit).collect();
                let defect: Vec<_> = scored.iter().filter(|s| !s.2)
                    .take(candidate_limit).collect();
                strict.into_iter().chain(defect).collect()
            } else {
                scored.iter().take(candidate_limit).collect()
            };
        let indices: Vec<usize> = selected.iter().map(|s| s.1).collect();
        let inners: Vec<[usize; 3]> = selected.iter().map(|s| s.3).collect();
        (indices, inners)
    });
    Ok(out)
}

#[pyfunction]
#[allow(clippy::too_many_arguments)]
fn simplex_bernstein_controls<'py>(
    py: Python<'py>,
    stack0: PyReadonlyArray3<'py, f64>,
    stack1: PyReadonlyArray3<'py, f64>,
    stack2: PyReadonlyArray3<'py, f64>,
    keys: [(usize, usize, usize, usize, i64, usize); 3],
    triangle: [[f64; 3]; 3],
    centers: [f64; 3],
    radii: [f64; 3],
    inner_indices: [usize; 3],
    multiplier: f64,
) -> PyResult<Vec<f64>> {
    let guard = TABLES.lock().unwrap();
    let tables = guard.as_ref().expect("install first");
    let s0 = stack0.as_slice()?;
    let s1 = stack1.as_slice()?;
    let s2 = stack2.as_slice()?;
    let stacks: [&[f64]; 3] = [s0, s1, s2];
    let contacts = [contact_from_key(keys[0]), contact_from_key(keys[1]),
                    contact_from_key(keys[2])];
    Ok(py.allow_threads(|| {
        simplex_controls(tables, &stacks, &triangle, &contacts, &centers,
                         &radii, &inner_indices, multiplier)
    }))
}
