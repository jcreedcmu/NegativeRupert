#!/usr/bin/env python3
"""Bottom-up exact compaction of a completed Nopert #214 global table.

The search deliberately commits a leaf as soon as it finds a certificate for
the current cell.  Consequently, certificates discovered in its children are
not normally retried on the parent.  This pass does that retry, but rebuilds
and exactly audits every proposed certificate on the larger parent cell.  No
floating-point search result or child validity is used as proof of a parent.
"""

import argparse
import json
import time

from nopert214_certificate_search import (
    PROJECTIVE_CERTIFICATE_DENOMINATOR,
    Q,
    atlas_fundamental_status,
    atlas_projective_global_triangle,
    atlas_projective_mismatch_radius,
    atlas_simplex_edge_smoke,
    compact_projective_local_axis_artifact,
    exact_certificate,
    interval_outside_cayley_ball,
    projective_local_reaudit_certificate,
)


SPLIT_KINDS = ("relative_split", "view_split")
AXIS_KEYS = (
    "edge_start", "edge_finish", "edge_start2", "edge_finish2", "mix",
    "support_index", "nonzero_witness", "B",
)


def qtuple(values):
    return tuple(map(Q, values))


def triangle_q(row):
    return tuple(qtuple(corner) for corner in row["triangle"])


def cell_point(row):
    center = tuple(float(Q(value)) for value in row["center"])
    triangle = triangle_q(row)
    centroid = tuple(float(sum(corner[i] for corner in triangle) / 3)
                     for i in range(3))
    return center + centroid


def axis_candidate(axis):
    return {"contacts": [{
        "vertex": int(axis["support_index"][i]),
        "edge_start": int(axis["edge_start"][i]),
        "edge_finish": int(axis["edge_finish"][i]),
        "edge_start2": int(axis["edge_start2"][i]),
        "edge_finish2": int(axis["edge_finish2"][i]),
        "mix": int(axis["mix"][i]),
    } for i in range(3)]}


def leaf_representatives(row):
    point = cell_point(row)
    kind = row["kind"]
    if kind == "global":
        return [(point, "global", axis_candidate(
            row["certificate"]["axis"]))]
    if kind == "mixed_global":
        # A component of a convex mixed certificate can sometimes certify a
        # slightly larger parent by itself.  Trying it as an ordinary global
        # leaf is exact and avoids needing a separate mixed-parent theorem.
        return [(point, "global", axis_candidate(component["axis"]))
                for component in row["certificate"]["components"]]
    if kind == "edge":
        certificate = row["certificate"]
        return [(point, "edge", {
            "cycle": tuple(map(int, certificate["cycle"])),
            "inner_indices": tuple(int(contact["inner_index"])
                                   for contact in certificate["contacts"]),
        })]
    if kind == "local":
        certificate = row["certificate"]
        return [(point, "local", {
            "symmetry_index": int(certificate["symmetry_index"]),
            "certificates": certificate["certificates"],
        })]
    if kind == "symmetry_tube":
        return [(point, "tube", {
            "symmetry_index": int(row["symmetry_index"]),
            "radius": Q(row["radius"]),
            "shared_index": int(row["shared_index"]),
            "root": int(row["root"]),
            "triangle": triangle_q(row),
        })]
    return []


def distance_sq(left, right):
    return sum((a-b)*(a-b) for a, b in zip(left, right))


def select_representatives(candidates, point, limit):
    # Preserve a small nearest set of every theorem family.  A single total
    # cap tends to discard the rarer local/tube candidates behind plentiful
    # edge leaves, even though the families certify different strata.
    selected = []
    # Edge audits are substantially cheaper than polynomial-global audits
    # and dominate successful view-parent collapses, so try them first.
    for kind in ("edge", "global", "local", "tube"):
        same_kind = [candidate for candidate in candidates
                     if candidate[1] == kind]
        same_kind.sort(key=lambda candidate:
                       distance_sq(point, candidate[0]))
        selected.extend(same_kind[:limit])
    return selected


def common_row(parent, kind):
    return {
        "id": int(parent["id"]),
        "kind": kind,
        "center": parent["center"],
        "widths": parent["widths"],
        "root": int(parent["root"]),
        "triangle": parent["triangle"],
        "view_depth": int(parent["view_depth"]),
    }


def exact_parent_leaf(chart, parent, candidates):
    center = qtuple(parent["center"])
    widths = qtuple(parent["widths"])
    triangle = triangle_q(parent)
    root = int(parent["root"])

    if interval_outside_cayley_ball(center, widths):
        return common_row(parent, "radius")

    fundamental_status, direction, _ = atlas_fundamental_status(
        chart, center, widths)
    if fundamental_status == "outside":
        return {**common_row(parent, "fundamental_prune"),
                "direction": direction}

    for _, kind, certificate in candidates:
        if kind == "edge":
            result = atlas_simplex_edge_smoke(
                chart, center, widths, triangle,
                certificate["cycle"], certificate["inner_indices"])
            if result is not None and result["accepted"]:
                return {**common_row(parent, "edge"), "certificate": {
                    "cycle": result["cycle"],
                    "contacts": result["contacts"],
                    "ball_multipliers": result["ball_multipliers"],
                }}
        elif kind == "global":
            result = atlas_projective_global_triangle(
                chart, center, widths, root, triangle,
                selected_candidate=certificate)
            if result is not None and result["accepted"]:
                axis = result["certificate"]
                return {**common_row(parent, "global"), "certificate": {
                    "axis": {key: axis[key] for key in AXIS_KEYS},
                    "inner_index": result["inner_index"],
                    "ball_multiplier": result["ball_multiplier"],
                }}
        elif kind == "local":
            result = projective_local_reaudit_certificate(
                triangle, certificate["certificates"])
            if result is None:
                continue
            c = result["c"]
            exact_r, _, _ = atlas_projective_mismatch_radius(
                chart, certificate["symmetry_index"], center, widths)
            r = exact_certificate.ceil_to(
                exact_r, PROJECTIVE_CERTIFICATE_DENOMINATOR)
            if r*r*(1+c*c) <= 4*c*c:
                return {**common_row(parent, "local"), "certificate": {
                    "symmetry_index": certificate["symmetry_index"],
                    "certificates": [
                        compact_projective_local_axis_artifact(axis)
                        for axis in result["certificates"]],
                    "c": c,
                    "delta": result["delta"],
                    "r": r,
                }}
        elif kind == "tube":
            # Shared tables cover one exact projective triangle.  A tube may
            # grow through pose splits, never through a view split.
            if (root != certificate["root"] or
                    triangle != certificate["triangle"]):
                continue
            exact_r, _, _ = atlas_projective_mismatch_radius(
                chart, certificate["symmetry_index"], center, widths)
            if exact_r <= certificate["radius"]:
                return {**common_row(parent, "symmetry_tube"),
                        "symmetry_index": certificate["symmetry_index"],
                        "radius": certificate["radius"],
                        "shared_index": certificate["shared_index"]}
    return None


def compact(data, representatives_per_kind):
    rows = data["rows"]
    chart = int(data["chart"])
    representatives = {}
    attempts = 0
    replacements = 0
    started = time.monotonic()

    for row in reversed(rows):
        row_id = int(row["id"])
        if row["kind"] == "view_root":
            representatives[row_id] = []
            continue
        if row["kind"] not in SPLIT_KINDS:
            representatives[row_id] = leaf_representatives(row)
            continue
        candidates = []
        for child in row["children"]:
            # Every generated row has exactly one parent.  Once that parent
            # consumes a child's representatives, retaining them only makes
            # the auxiliary map grow linearly with a six-figure table.
            candidates.extend(representatives.pop(int(child), ()))
        point = cell_point(row)
        candidates = select_representatives(
            candidates, point, representatives_per_kind)
        attempts += len(candidates)
        replacement = exact_parent_leaf(chart, row, candidates)
        if replacement is None:
            representatives[row_id] = candidates
        else:
            rows[row_id] = replacement
            representatives[row_id] = leaf_representatives(replacement)
            replacements += 1
        processed = len(rows)-row_id
        if processed % 1000 == 0:
            print(f"audited {processed}/{len(rows)} rows: "
                  f"{replacements} replacements, {attempts} candidates",
                  flush=True)

    reachable = set()

    def mark(row_id):
        if row_id in reachable:
            return
        reachable.add(row_id)
        row = rows[row_id]
        if row["kind"] == "view_root":
            mark(int(row["child"]))
        elif row["kind"] in SPLIT_KINDS:
            for child in row["children"]:
                mark(int(child))

    mark(0)
    old_ids = sorted(reachable)
    remap = {old: new for new, old in enumerate(old_ids)}
    compact_rows = []
    for old_id in old_ids:
        row = dict(rows[old_id])
        row["id"] = remap[old_id]
        if row["kind"] == "view_root":
            row["child"] = remap[int(row["child"])]
        elif row["kind"] in SPLIT_KINDS:
            row["children"] = [remap[int(child)]
                               for child in row["children"]]
        compact_rows.append(row)

    data["rows"] = compact_rows
    data["pending"] = []
    data["failures"] = []
    data["complete"] = True
    for kind in ("view_root", *SPLIT_KINDS, "edge", "global", "local",
                 "symmetry_tube", "radius", "fundamental_prune",
                 "mixed_global"):
        data["counts"][kind] = sum(row["kind"] == kind
                                    for row in compact_rows)
    data["counts"]["nearby_parent_prunes"] = replacements
    elapsed = time.monotonic()-started
    return len(rows), len(compact_rows), replacements, attempts, elapsed


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("input")
    parser.add_argument("output")
    parser.add_argument("--representatives", type=int, default=8,
                        help="nearest candidates retained per theorem family")
    args = parser.parse_args()
    if args.representatives < 1:
        parser.error("--representatives must be positive")

    with open(args.input, encoding="utf-8") as source:
        data = json.load(source)
    if not data.get("complete") or data.get("pending") or data.get("failures"):
        raise SystemExit("refusing to compact an incomplete global table")
    rows = data["rows"]
    if any(row is None for row in rows):
        raise SystemExit("completed global table contains an empty row")
    if any(int(row["id"]) != i for i, row in enumerate(rows)):
        raise SystemExit("global rows are not indexed densely")

    before, after, replacements, attempts, elapsed = compact(
        data, args.representatives)
    with open(args.output, "w", encoding="utf-8") as output:
        json.dump(data, output, default=str)
    print(f"compacted {before} to {after} rows using {replacements} exact "
          f"parent replacements and {attempts} candidate audits in "
          f"{elapsed:.3f}s")


if __name__ == "__main__":
    main()
