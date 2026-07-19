"""Numerical reconnaissance for a non-Rupert proof of the snub cube.

The experiment works in the same five angular coordinates as the
Noperthedron proof.  For a pose

    (theta_inner, phi_inner, theta_outer, phi_outer, alpha)

the two projected vertex sets are

    B = R(alpha) M(theta_inner, phi_inner) V
    A =          M(theta_outer, phi_outer) V.

Translations are *not* included as search parameters.  For fixed A and B,
write the outer polygon as

    A = {x : u_j . x <= h_A(u_j)}.

The largest uniform clearance s for a translate B+t is the LP

    maximize s,  u_j . t + s <= h_A(u_j) - h_B(u_j).

Its dual has nonnegative weights lambda with

    sum lambda_j u_j = 0,  sum lambda_j = 1.

In dimension two an optimum uses at most three normals.  We enumerate all
pairs and triples, so ``clearance`` is the exact LP answer apart from normal
floating-point error.  A nonpositive answer rules out strict containment.

We separately test the two-normal (width) obstruction.  This is equivalent
to asking whether the difference polygon B-B lies strictly inside A-A.

The script performs four kinds of reconnaissance:

* Haar-random samples in the five-dimensional pose space;
* perturbations around every rotational symmetry (the equality strata);
* local optimization of the poses with the largest translation clearance;
* a conservative first-order ``box radius`` estimate.  If C=-clearance is
  the balanced-support margin and rho is the vertex radius, then the same
  fixed certificate covers every coordinate box with sum of radii < C/rho.

This is deliberately not a formal certificate generator.  Its purpose is to
answer whether width/two-contact leaves cover most poses, whether three-
contact leaves close the remainder, and whether the near-zero set consists
only of the expected symmetry copies of the identity pose.
"""

from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import time
from dataclasses import dataclass

import numpy as np
from scipy.optimize import minimize
from scipy.spatial import ConvexHull


TAU = 2.0 * math.pi
TRIBONACCI = 1.8392867552141612
PARAM_PERIODIC = np.array([True, False, True, False, True])
PARAM_LO = np.array([-math.pi, 0.0, -math.pi, 0.0, -math.pi])
PARAM_HI = np.array([math.pi, math.pi, math.pi, math.pi, math.pi])


def permutation_parity(p: tuple[int, int, int]) -> int:
    inv = sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3))
    return inv & 1


def snub_cube_vertices(t: float = TRIBONACCI) -> np.ndarray:
    """One chirality of the standard 24-vertex snub cube."""
    base = np.array([1.0, 1.0 / t, t])
    out = []
    for p in itertools.permutations(range(3)):
        parity = permutation_parity(p)
        for signs in itertools.product((-1.0, 1.0), repeat=3):
            nplus = sum(s > 0 for s in signs)
            if (nplus & 1) == parity:
                out.append(base[list(p)] * np.array(signs))
    verts = np.unique(np.round(np.array(out), 15), axis=0)
    if verts.shape != (24, 3):
        raise AssertionError(verts.shape)
    return verts


VERTS = snub_cube_vertices()
VERTEX_RADIUS = float(np.linalg.norm(VERTS[0]))
UNIT_VERTS = VERTS / VERTEX_RADIUS


def projection_matrix(theta: float, phi: float) -> np.ndarray:
    st, ct = math.sin(theta), math.cos(theta)
    sf, cf = math.sin(phi), math.cos(phi)
    return np.array([[-st, ct, 0.0], [-ct * cf, -st * cf, sf]])


def frame_matrix(theta: float, phi: float) -> np.ndarray:
    m = projection_matrix(theta, phi)
    return np.vstack((m, np.cross(m[0], m[1])))


def rot2(alpha: float) -> np.ndarray:
    sa, ca = math.sin(alpha), math.cos(alpha)
    return np.array([[ca, -sa], [sa, ca]])


def project_pose(pose: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    ti, fi, to, fo, alpha = pose
    inner_map = rot2(alpha) @ projection_matrix(ti, fi)
    outer_map = projection_matrix(to, fo)
    return VERTS @ outer_map.T, VERTS @ inner_map.T


def signed_permutation_rotations() -> np.ndarray:
    mats = []
    for p in itertools.permutations(range(3)):
        for signs in itertools.product((-1.0, 1.0), repeat=3):
            m = np.zeros((3, 3))
            for i, j in enumerate(p):
                m[i, j] = signs[i]
            if np.linalg.det(m) > 0.5:
                mats.append(m)
    mats = np.array(mats)
    if mats.shape != (24, 3, 3):
        raise AssertionError(mats.shape)
    return mats


SYMMETRIES = signed_permutation_rotations()


def relative_rotation(pose: np.ndarray) -> np.ndarray:
    """Rotation G for which equal shadows have inner_frame = outer_frame G."""
    ti, fi, to, fo, alpha = pose
    lift = np.eye(3)
    lift[:2, :2] = rot2(alpha)
    inner_frame = lift @ frame_matrix(ti, fi)
    outer_frame = frame_matrix(to, fo)
    return outer_frame.T @ inner_frame


def symmetry_distance(pose: np.ndarray) -> float:
    """Smallest SO(3) rotation angle from the relative pose to a symmetry."""
    rel = relative_rotation(pose)
    traces = np.einsum("nij,ji->n", SYMMETRIES, rel)
    cos_angles = np.clip((traces - 1.0) / 2.0, -1.0, 1.0)
    return float(np.arccos(cos_angles).min())


def hull_equations(points: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    hull = ConvexHull(points)
    # scipy equations: normal . x + offset <= 0; normals have unit length.
    return hull.equations[:, :2], -hull.equations[:, 2]


def supports(points: np.ndarray, normals: np.ndarray) -> np.ndarray:
    return (points @ normals.T).max(axis=0)


def balanced_dual(normals: np.ndarray, delta: np.ndarray):
    """Return minimum dual value and a <=3-normal certificate."""
    m = len(normals)
    best = math.inf
    best_idx = None
    best_lam = None

    # Opposite pairs are valid extreme points of the dual feasible polygon.
    for i in range(m):
        for j in range(i + 1, m):
            a = np.array([[normals[i, 0], normals[j, 0]],
                          [normals[i, 1], normals[j, 1]],
                          [1.0, 1.0]])
            lam, residual, _, _ = np.linalg.lstsq(a, np.array([0.0, 0.0, 1.0]), rcond=None)
            if np.linalg.norm(a @ lam - np.array([0.0, 0.0, 1.0])) < 2e-10 and lam.min() >= -2e-10:
                val = float(lam @ delta[[i, j]])
                if val < best:
                    best, best_idx, best_lam = val, (i, j), lam

    for idx in itertools.combinations(range(m), 3):
        a = np.vstack((normals[list(idx)].T, np.ones(3)))
        det = np.linalg.det(a)
        if abs(det) < 1e-12:
            continue
        lam = np.linalg.solve(a, np.array([0.0, 0.0, 1.0]))
        if lam.min() >= -2e-10:
            val = float(lam @ delta[list(idx)])
            if val < best:
                best, best_idx, best_lam = val, idx, lam
    if best_idx is None:
        raise RuntimeError("outer normals did not positively span the plane")
    best_lam = np.maximum(best_lam, 0.0)
    best_lam /= best_lam.sum()
    return best, tuple(int(i) for i in best_idx), best_lam


@dataclass
class PoseResult:
    clearance: float
    width_margin: float
    n_outer_edges: int
    dual_size: int
    symmetry_distance: float


def evaluate_pose(pose: np.ndarray, details: bool = False):
    outer, inner = project_pose(pose)
    normals, h_outer = hull_equations(outer)
    h_inner = supports(inner, normals)
    delta = h_outer - h_inner
    clearance, idx, lam = balanced_dual(normals, delta)

    # A width certificate is a balanced dual certificate on u and -u.
    # It suffices to inspect edge normals of the difference polygon A-A.
    outer_diff = (outer[:, None, :] - outer[None, :, :]).reshape(-1, 2)
    diff_normals, h_outer_diff = hull_equations(outer_diff)
    h_inner_diff = supports(inner, diff_normals) + supports(inner, -diff_normals)
    width_gap = h_inner_diff - h_outer_diff
    k = int(np.argmax(width_gap))
    # Divide by two so width_margin and -clearance use dual weights summing 1.
    width_margin = float(width_gap[k] / 2.0)

    result = PoseResult(
        clearance=float(clearance),
        width_margin=width_margin,
        n_outer_edges=len(normals),
        dual_size=len(idx),
        symmetry_distance=symmetry_distance(pose),
    )
    if not details:
        return result
    return result, {
        "outer": outer,
        "inner": inner,
        "normals": normals,
        "delta": delta,
        "dual_indices": idx,
        "dual_weights": lam,
        "dual_margin": -clearance,
        "width_direction": diff_normals[k],
        "width_margin": width_margin,
    }


def fixed_certificate(pose: np.ndarray, kind: str):
    """Extract fixed directions, weights and inner witnesses at one pose."""
    result, d = evaluate_pose(pose, details=True)
    if kind == "triple":
        dirs = d["normals"][list(d["dual_indices"])]
        weights = d["dual_weights"]
    elif kind == "width":
        u = d["width_direction"]
        dirs = np.array([u, -u])
        weights = np.array([0.5, 0.5])
    else:
        raise ValueError(kind)
    _, inner = project_pose(pose)
    inner_indices = np.argmax(inner @ dirs.T, axis=0)
    return dirs, weights, inner_indices


def fixed_certificate_box_slack(pose: np.ndarray, epsv: np.ndarray,
                                dirs: np.ndarray, weights: np.ndarray,
                                inner_indices: np.ndarray) -> float:
    """Second-order anisotropic lower bound for one fixed balanced certificate.

    This is the float analogue of summing two or three copies of the current
    anisotropic Global Theorem.  Vertices are normalized to radius one, and
    no rational-rounding kappa is charged here.
    """
    ti, fi, to, fo, alpha = pose
    e_ti, e_fi, e_to, e_fo, e_alpha = np.asarray(epsv, dtype=float)
    sti, cti, sfi, cfi = math.sin(ti), math.cos(ti), math.sin(fi), math.cos(fi)
    sto, cto, sfo, cfo = math.sin(to), math.cos(to), math.sin(fo), math.cos(fo)
    sa, ca = math.sin(alpha), math.cos(alpha)
    e_inner = e_alpha + e_ti + e_fi
    e_outer = e_to + e_fo
    total = 0.0

    for u, weight, si in zip(dirs, weights, inner_indices):
        u0, u1 = u
        sx, sy, sz = UNIT_VERTS[int(si)]
        m0 = -sti * sx + cti * sy
        m1 = -cti * cfi * sx - sti * cfi * sy + sfi * sz
        mt0 = -cti * sx - sti * sy
        mt1 = sti * cfi * sx - cti * cfi * sy
        mf1 = cti * sfi * sx + sti * sfi * sy + cfi * sz
        mtt0 = sti * sx - cti * sy
        mtt1 = cti * cfi * sx + sti * cfi * sy
        mtf1 = -sti * sfi * sx + cti * sfi * sy

        base_inner = (ca * m0 - sa * m1) * u0 + (sa * m0 + ca * m1) * u1
        q_aa = abs(base_inner)
        q_at = abs((-sa * mt0 - ca * mt1) * u0 + (ca * mt0 - sa * mt1) * u1)
        q_af = abs((-ca * mf1) * u0 + (-sa * mf1) * u1)
        q_tt = abs((ca * mtt0 - sa * mtt1) * u0 + (sa * mtt0 + ca * mtt1) * u1)
        q_tf = abs((-sa * mtf1) * u0 + (ca * mtf1) * u1)
        q_ff = abs((sa * m1) * u0 + (-ca * m1) * u1)
        d_a = abs((-sa * m0 - ca * m1) * u0 + (ca * m0 - sa * m1) * u1)
        d_t = abs((ca * mt0 - sa * mt1) * u0 + (sa * mt0 + ca * mt1) * u1)
        d_f = abs((-sa * mf1) * u0 + (ca * mf1) * u1)
        pen_inner = (
            e_alpha * d_a + e_ti * d_t + e_fi * d_f
            + 0.5 * (e_alpha**2 * q_aa + 2 * e_alpha * e_ti * q_at
                     + 2 * e_alpha * e_fi * q_af + e_ti**2 * q_tt
                     + 2 * e_ti * e_fi * q_tf + e_fi**2 * q_ff)
            + e_inner**3 / 6.0)

        px, py, pz = UNIT_VERTS.T
        mo0 = -sto * px + cto * py
        mo1 = -cto * cfo * px - sto * cfo * py + sfo * pz
        mot0 = -cto * px - sto * py
        mot1 = sto * cfo * px - cto * cfo * py
        mof1 = cto * sfo * px + sto * sfo * py + cfo * pz
        mott1 = cto * cfo * px + sto * cfo * py
        motf1 = -sto * sfo * px + cto * sfo * py
        base_outer = mo0 * u0 + mo1 * u1
        h_tt = np.abs(-mo0 * u0 + mott1 * u1)
        h_tf = np.abs(motf1 * u1)
        h_ff = np.abs(mo1 * u1)
        pen_outer = (
            e_to * np.abs(mot0 * u0 + mot1 * u1)
            + e_fo * np.abs(mof1 * u1)
            + 0.5 * (e_to**2 * h_tt + 2 * e_to * e_fo * h_tf + e_fo**2 * h_ff)
            + e_outer**3 / 6.0)
        directional = base_inner - pen_inner - np.max(base_outer + pen_outer)
        total += float(weight) * directional
    return total


def certificate_isotropic_radius(pose: np.ndarray, kind: str,
                                 upper: float = 0.25) -> float:
    dirs, weights, inner_indices = fixed_certificate(pose, kind)

    return certificate_data_isotropic_radius(
        pose, dirs, weights, inner_indices, upper=upper)


def certificate_data_isotropic_radius(pose: np.ndarray, dirs: np.ndarray,
                                       weights: np.ndarray,
                                       inner_indices: np.ndarray,
                                       upper: float = 0.25) -> float:

    def slack(e):
        return fixed_certificate_box_slack(
            pose, np.full(5, e), dirs, weights, inner_indices)

    if slack(0.0) <= 1e-13:
        return 0.0
    lo, hi = 0.0, upper
    if slack(hi) > 0.0:
        return hi
    for _ in range(42):
        mid = (lo + hi) / 2.0
        if slack(mid) > 0.0:
            lo = mid
        else:
            hi = mid
    return lo


def all_balanced_extremes(normals: np.ndarray) -> list[np.ndarray]:
    """All <=3-supported extreme points of the balanced-weight polytope."""
    m = len(normals)
    rhs = np.array([0.0, 0.0, 1.0])
    rows = []
    for size in (2, 3):
        for idx in itertools.combinations(range(m), size):
            a = np.vstack((normals[list(idx)].T, np.ones(size)))
            if size == 2:
                lam, _, _, _ = np.linalg.lstsq(a, rhs, rcond=None)
                if np.linalg.norm(a @ lam - rhs) > 2e-10:
                    continue
            else:
                if abs(np.linalg.det(a)) < 1e-12:
                    continue
                lam = np.linalg.solve(a, rhs)
            if lam.min() < -2e-10:
                continue
            lam = np.maximum(lam, 0.0); lam /= lam.sum()
            row = np.zeros(m); row[list(idx)] = lam
            rows.append(row)
    return [r for r in np.unique(np.round(np.array(rows), 14), axis=0)]


def robust_certificate_isotropic_radius(pose: np.ndarray, upper: float = 0.25):
    """Search every outer-facet width certificate and balanced dual extreme.

    The LP-optimal center certificate need not cover the largest box: a
    slightly smaller center margin can have much smaller angular derivatives.
    This routine measures that effect and is intentionally more expensive.
    """
    outer, inner = project_pose(pose)
    normals, h_outer = hull_equations(outer)
    h_inner = supports(inner, normals)
    delta = h_outer - h_inner
    best = 0.0
    best_kind = None

    for lam in all_balanced_extremes(normals):
        center_margin = -float(lam @ delta)
        if center_margin <= 1e-13:
            continue
        take = np.flatnonzero(lam > 1e-12)
        dirs = normals[take]
        weights = lam[take]; weights /= weights.sum()
        inner_indices = np.argmax(inner @ dirs.T, axis=0)
        radius = certificate_data_isotropic_radius(
            pose, dirs, weights, inner_indices, upper=upper)
        if radius > best:
            best, best_kind = radius, f"balanced-{len(take)}"

    outer_diff = (outer[:, None, :] - outer[None, :, :]).reshape(-1, 2)
    diff_normals, h_outer_diff = hull_equations(outer_diff)
    for u, hout in zip(diff_normals, h_outer_diff):
        gap = float(supports(inner, u[None, :])[0]
                    + supports(inner, (-u)[None, :])[0] - hout) / 2.0
        if gap <= 1e-13:
            continue
        dirs = np.array([u, -u]); weights = np.array([0.5, 0.5])
        inner_indices = np.argmax(inner @ dirs.T, axis=0)
        radius = certificate_data_isotropic_radius(
            pose, dirs, weights, inner_indices, upper=upper)
        if radius > best:
            best, best_kind = radius, "width"
    return best, best_kind


def random_poses(rng: np.random.Generator, n: int) -> np.ndarray:
    poses = np.empty((n, 5))
    poses[:, 0] = rng.uniform(-math.pi, math.pi, n)
    poses[:, 2] = rng.uniform(-math.pi, math.pi, n)
    poses[:, 4] = rng.uniform(-math.pi, math.pi, n)
    poses[:, 1] = np.arccos(rng.uniform(-1.0, 1.0, n))
    poses[:, 3] = np.arccos(rng.uniform(-1.0, 1.0, n))
    return poses


def wrap_pose(x: np.ndarray) -> np.ndarray:
    y = np.array(x, dtype=float)
    for i in (0, 2, 4):
        y[i] = (y[i] + math.pi) % TAU - math.pi
    # Reflection across a pole can be represented by shifting theta by pi.
    for ti, fi in ((0, 1), (2, 3)):
        while y[fi] < 0.0 or y[fi] > math.pi:
            if y[fi] < 0.0:
                y[fi] = -y[fi]
                y[ti] += math.pi
            if y[fi] > math.pi:
                y[fi] = TAU - y[fi]
                y[ti] += math.pi
            y[ti] = (y[ti] + math.pi) % TAU - math.pi
    return y


def summarize(results: list[PoseResult]) -> dict:
    clear = np.array([r.clearance for r in results])
    width = np.array([r.width_margin for r in results])
    dist = np.array([r.symmetry_distance for r in results])
    eps = 2e-10
    triple_margin = -clear
    out = {
        "count": len(results),
        "width_reject_fraction": float(np.mean(width >= -eps)),
        "three_contact_only_fraction": float(np.mean((width < -eps) & (clear <= eps))),
        "apparent_strict_fit_fraction": float(np.mean(clear > eps)),
        "clearance_quantiles": dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(clear, [0, .01, .1, .5, .9, .99, 1])))),
        "width_margin_quantiles": dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(width, [0, .01, .1, .5, .9, .99, 1])))),
        "symmetry_distance_quantiles": dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(dist, [0, .01, .1, .5, .9, .99, 1])))),
        "l1_box_radius_quantiles": dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(np.maximum(triple_margin, 0.0) / VERTEX_RADIUS,
                                   [0, .01, .1, .5, .9, .99, 1])))),
    }
    return out


def equality_pose(theta: float, phi: float, symmetry: np.ndarray) -> np.ndarray:
    """Numerically recover pose coordinates whose relative rotation is symmetry.

    This helper starts with a chosen outer frame and decomposes outer_frame G
    into alpha/theta/phi.  It is used only to seed structured perturbations.
    """
    fo = frame_matrix(theta, phi)
    target = fo @ symmetry
    n = target[2]
    fi = math.acos(float(np.clip(n[2], -1.0, 1.0)))
    if math.sin(fi) > 1e-10:
        ti = math.atan2(n[1], n[0])
    else:
        ti = 0.0
    base = frame_matrix(ti, fi)
    q = target @ base.T
    alpha = math.atan2(q[1, 0], q[0, 0])
    pose = wrap_pose(np.array([ti, fi, theta, phi, alpha]))
    if symmetry_distance(pose) > 2e-7:
        raise AssertionError(symmetry_distance(pose))
    return pose


def pose_from_relative(theta: float, phi: float, relative: np.ndarray) -> np.ndarray:
    """Pose with the chosen outer view and prescribed relative SO(3) matrix."""
    target = frame_matrix(theta, phi) @ relative
    n = target[2]
    fi = math.acos(float(np.clip(n[2], -1.0, 1.0)))
    if math.sin(fi) > 1e-10:
        ti = math.atan2(n[1], n[0])
    else:
        ti = 0.0
    base = frame_matrix(ti, fi)
    q = target @ base.T
    alpha = math.atan2(q[1, 0], q[0, 0])
    return wrap_pose(np.array([ti, fi, theta, phi, alpha]))


def axis_angle(axis: np.ndarray, angle: float) -> np.ndarray:
    axis = np.asarray(axis, dtype=float)
    axis /= np.linalg.norm(axis)
    x, y, z = axis
    k = np.array([[0.0, -z, y], [z, 0.0, -x], [-y, x, 0.0]])
    return np.eye(3) + math.sin(angle) * k + (1.0 - math.cos(angle)) * (k @ k)


def structured_near_symmetry(rng: np.random.Generator, per_scale: int):
    records = []
    scales = [1e-1, 3e-2, 1e-2, 3e-3, 1e-3, 3e-4, 1e-4]
    for scale in scales:
        for _ in range(per_scale):
            theta = rng.uniform(-math.pi, math.pi)
            phi = math.acos(rng.uniform(-1.0, 1.0))
            sym = SYMMETRIES[rng.integers(len(SYMMETRIES))]
            p0 = equality_pose(theta, phi, sym)
            direction = rng.normal(size=5)
            direction /= np.linalg.norm(direction)
            p = wrap_pose(p0 + scale * direction)
            r = evaluate_pose(p)
            records.append((scale, p, r))
    return records


def relative_rotation_cone(rng: np.random.Generator, per_scale: int):
    """Probe normal directions to the two-dimensional equality strata.

    The outer view is held fixed.  The inner copy is changed by a relative
    three-dimensional rotation of exactly ``scale`` radians about a Haar-
    random axis.  This avoids wasting perturbation on directions tangent to
    the equality stratum.
    """
    records = []
    scales = [1e-2, 1e-3, 1e-4, 1e-5, 1e-6]
    for scale in scales:
        for _ in range(per_scale):
            theta = rng.uniform(-math.pi, math.pi)
            phi = math.acos(rng.uniform(-1.0, 1.0))
            axis = rng.normal(size=3)
            axis /= np.linalg.norm(axis)
            sym = SYMMETRIES[rng.integers(len(SYMMETRIES))]
            relative = sym @ axis_angle(axis, scale)
            pose = pose_from_relative(theta, phi, relative)
            r = evaluate_pose(pose)
            records.append((scale, pose, axis, r))
    return records


def optimize_top(poses: np.ndarray, results: list[PoseResult], n_starts: int,
                 maxiter: int):
    order = np.argsort([-r.clearance for r in results])[:n_starts]
    optimized = []

    def objective(x):
        return -evaluate_pose(wrap_pose(x)).clearance

    for rank, i in enumerate(order):
        x0 = poses[i]
        ans = minimize(objective, x0, method="Nelder-Mead",
                       options={"maxiter": maxiter, "xatol": 2e-9, "fatol": 2e-11})
        p = wrap_pose(ans.x)
        r = evaluate_pose(p)
        optimized.append({
            "start_rank": rank,
            "success": bool(ans.success),
            "iterations": int(ans.nit),
            "pose": p.tolist(),
            "clearance": r.clearance,
            "width_margin": r.width_margin,
            "symmetry_distance": r.symmetry_distance,
        })
    return optimized


def geometry_sanity() -> dict:
    hull = ConvexHull(VERTS)
    d = np.linalg.norm(VERTS[:, None] - VERTS[None, :], axis=2)
    nonzero = d[d > 1e-9]
    edge = float(nonzero.min())
    edge_pairs = int(np.sum(np.isclose(d, edge, atol=2e-9)) // 2)
    return {
        "vertices": len(VERTS),
        "triangulated_hull_facets": len(hull.simplices),
        "edge_length": edge,
        "edge_pairs": edge_pairs,
        "vertex_radius": VERTEX_RADIUS,
        "symmetry_count": len(SYMMETRIES),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=20000)
    ap.add_argument("--near-per-scale", type=int, default=500)
    ap.add_argument("--cone-per-scale", type=int, default=1000)
    ap.add_argument("--optimize-starts", type=int, default=12)
    ap.add_argument("--optimize-iters", type=int, default=1200)
    ap.add_argument("--box-samples", type=int, default=1000)
    ap.add_argument("--seed", type=int, default=20260718)
    ap.add_argument("--out", default=os.path.join(os.path.dirname(__file__),
                                                   "snub_cube_experiment.json"))
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    t0 = time.time()

    sanity = geometry_sanity()
    print("geometry", sanity, flush=True)
    poses = random_poses(rng, args.samples)
    results = []
    for i, p in enumerate(poses):
        results.append(evaluate_pose(p))
        if (i + 1) % 1000 == 0:
            print(f"random {i + 1}/{args.samples}  elapsed={time.time() - t0:.1f}s", flush=True)
    random_summary = summarize(results)
    print("random summary", json.dumps(random_summary, indent=2), flush=True)

    near = structured_near_symmetry(rng, args.near_per_scale)
    near_summary = {}
    for scale in sorted(set(x[0] for x in near), reverse=True):
        rs = [x[2] for x in near if x[0] == scale]
        near_summary[str(scale)] = summarize(rs)
    print("near-symmetry summaries", json.dumps(near_summary, indent=2), flush=True)

    cone = relative_rotation_cone(rng, args.cone_per_scale)
    cone_summary = {}
    for scale in sorted(set(x[0] for x in cone), reverse=True):
        rs = [x[3] for x in cone if x[0] == scale]
        summary = summarize(rs)
        summary["triple_margin_over_angle_quantiles"] = dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(np.array([-r.clearance for r in rs]) / scale,
                                   [0, .01, .1, .5, .9, .99, 1]))))
        summary["width_margin_over_angle_quantiles"] = dict(zip(
            ("min", "p01", "p10", "median", "p90", "p99", "max"),
            map(float, np.quantile(np.array([r.width_margin for r in rs]) / scale,
                                   [0, .01, .1, .5, .9, .99, 1]))))
        cone_summary[str(scale)] = summary
    print("relative-rotation cone summaries", json.dumps(cone_summary, indent=2), flush=True)

    optimized = optimize_top(poses, results, args.optimize_starts, args.optimize_iters)
    print("optimized", json.dumps(optimized, indent=2), flush=True)

    box_n = min(args.box_samples, len(poses))
    box_rows = []
    for i in range(box_n):
        rt = certificate_isotropic_radius(poses[i], "triple")
        rw = certificate_isotropic_radius(poses[i], "width")
        box_rows.append((rw, rt))
    box_arr = np.array(box_rows) if box_rows else np.empty((0, 2))
    box_summary = {}
    if len(box_arr):
        names = ("min", "p01", "p10", "median", "p90", "p99", "max")
        qs = [0, .01, .1, .5, .9, .99, 1]
        box_summary = {
            "count": len(box_arr),
            "width_radius_quantiles": dict(zip(names, map(float, np.quantile(box_arr[:, 0], qs)))),
            "triple_radius_quantiles": dict(zip(names, map(float, np.quantile(box_arr[:, 1], qs)))),
            "best_radius_quantiles": dict(zip(names, map(float, np.quantile(box_arr.max(axis=1), qs)))),
            "triple_improves_fraction": float(np.mean(box_arr[:, 1] > box_arr[:, 0] + 1e-12)),
        }
    print("second-order box radii", json.dumps(box_summary, indent=2), flush=True)

    # Preserve the most informative poses for reproducibility without emitting
    # all random samples.  Highest clearance means hardest for the triple cert;
    # most negative width margin means strongest need for three contacts.
    hard = np.argsort([-r.clearance for r in results])[:50]
    asymmetric = np.argsort([r.width_margin for r in results])[:50]
    payload = {
        "parameters": vars(args),
        "elapsed_seconds": time.time() - t0,
        "geometry": sanity,
        "random": random_summary,
        "near_symmetry": near_summary,
        "relative_rotation_cone": cone_summary,
        "optimized": optimized,
        "second_order_box_radii": box_summary,
        "second_order_box_samples": [
            {
                "pose": poses[i].tolist(),
                "symmetry_distance": results[i].symmetry_distance,
                "width_radius": float(box_arr[i, 0]),
                "triple_radius": float(box_arr[i, 1]),
                "best_radius": float(max(box_arr[i])),
            }
            for i in range(len(box_arr))
        ],
        "hard_random_poses": [
            {"pose": poses[i].tolist(), **results[i].__dict__} for i in hard],
        "strongly_asymmetric_poses": [
            {"pose": poses[i].tolist(), **results[i].__dict__} for i in asymmetric],
        "near_symmetry_width_failures": [
            {"scale": scale, "pose": pose.tolist(), **result.__dict__}
            for scale, pose, result in near if result.width_margin < 0.0],
        "cone_width_failures": [
            {"scale": scale, "pose": pose.tolist(), "axis": axis.tolist(),
             **result.__dict__}
            for scale, pose, axis, result in cone if result.width_margin < 0.0],
    }
    with open(args.out, "w") as f:
        json.dump(payload, f, indent=2)
        f.write("\n")
    print(f"wrote {args.out}", flush=True)


if __name__ == "__main__":
    main()
