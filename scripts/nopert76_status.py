#!/usr/bin/env python3
"""One-shot status report for the Nopert #76 non-Rupert program.

Usage:
  python3 scripts/nopert76_status.py            # quick status
  python3 scripts/nopert76_status.py --deep     # + chart-0 pending-cell autopsy

Reads the newest chart run logs, the live local-verification log (if any),
process/memory state, and a snapshot file to show progress rates between
invocations.  The --deep autopsy streams only the tail of the 2GB chart-0
checkpoint, so it is cheap; a passage would show up there as a persistent,
deepening pending cluster (view depth near the cap) — the healthy signature
is shallow scattered cells and zero failures.

Also reports the exact uncertified parameter-space volume per chart
(sum over pending cells of 4^-view_depth * prod widths/root_widths).
Volume measures coverage, not remaining work: the DFS drills the razor-thin
hard cells first while most volume waits in fat, easy, unstarted cells that
sweep out quickly at the end — expect ~100% for most of a run, then a cliff.
"""

import argparse
import json
import mmap
import math
import re
import subprocess
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

ART = Path(__file__).resolve().parents[1] / ".artifacts/nopert76"
SNAPSHOT = ART / ".status_snapshot.json"
CHARTS = [0, 1, 2]


def latest_checkpoint_line(chart):
    logs = sorted(ART.glob(f"chart{chart}-run*.log"),
                  key=lambda p: p.stat().st_mtime)
    for log in reversed(logs):
        for raw in reversed(log.read_text().splitlines()):
            raw = raw.strip()
            if raw.startswith("{"):
                try:
                    return json.loads(raw), log
                except json.JSONDecodeError:
                    continue
    return None, None


def fmt_delta(new, old, dt_h):
    if old is None or dt_h < 0.05:
        return ""
    return f" ({new - old:+,} / {(new - old) / dt_h:,.0f} per h)"


def chart_status(prev, now):
    for chart in CHARTS:
        state, log = latest_checkpoint_line(chart)
        if state is None:
            print(f"chart {chart}: no checkpoint log found")
            continue
        old = prev.get(f"chart{chart}", {})
        dt_h = (now - prev.get("time", now)) / 3600
        rows, pending = state["rows"], state["pending"]
        failures = state["failures"]
        if isinstance(failures, list):
            failures = len(failures)
        flag = "" if failures == 0 else "  *** FAILURES ***"
        done = " COMPLETE" if state.get("complete") else ""
        age_min = (time.time() - log.stat().st_mtime) / 60
        stale = "" if age_min < 30 else f"  [log idle {age_min/60:.1f}h]"
        print(f"chart {chart}: rows {rows:,}{fmt_delta(rows, old.get('rows'), dt_h)}, "
              f"pending {pending:,}{fmt_delta(pending, old.get('pending'), dt_h)}, "
              f"failures {failures}{flag}{done}{stale}")
        prev[f"chart{chart}"] = {"rows": rows, "pending": pending}


# --restricted-fundamental-root Cayley boxes (see the generator).
ROOT_WIDTHS = {0: (Q(1), Q(1), Q(1, 3)),
               1: (Q(1), Q(1, 3), Q(1)),
               2: (Q(1, 3), Q(1), Q(1))}


def checkpoint_tail_array(buf, key):
    """Decode a top-level array that follows the giant "rows" array."""
    i = buf.rfind(b'"%s":' % key)
    if i < 0:
        raise ValueError(f"no {key.decode()} array in checkpoint")
    text = buf[i + len(key) + 3:].decode()
    value, _ = json.JSONDecoder().raw_decode(
        text, len(text) - len(text.lstrip()))
    return value


def volume_status(prev, now):
    dt_h = (now - prev.get("time", now)) / 3600
    for chart in CHARTS:
        path = ART / f"chart{chart}.json"
        if not path.exists():
            continue
        try:
            with open(path, "rb") as f:
                buf = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
            pending = checkpoint_tail_array(buf, b"pending")
            failures = checkpoint_tail_array(buf, b"failures")
            buf.close()
        except (ValueError, json.JSONDecodeError) as error:
            print(f"volume: chart {chart}: unreadable ({error})")
            continue
        cells = ([(s[2], s[5]) for s in pending] +
                 [(f["widths"], f["view_depth"]) for f in failures])
        if not cells:
            print(f"volume: chart {chart}: 0 remaining (complete)")
            continue
        total = Q(0)
        deep = Q(0)
        deep_cells = 0
        for widths, view_depth in cells:
            frac = Q(1, 4) ** view_depth
            for w, root_w in zip(map(Q, widths), ROOT_WIDTHS[chart]):
                frac *= w / root_w
            total += frac
            if view_depth >= 4:
                deep += frac
                deep_cells += 1
        age_min = (time.time() - path.stat().st_mtime) / 60

        def delta(key, new):
            old = prev.get(key)
            prev[key] = new
            if old is None or dt_h < 0.05 or new == old:
                return ""
            return f" [{new - old:+.3e}, {(new - old) / dt_h:+.2e}/h]"

        # The percent is dominated by fat unstarted depth<=3 cells and sits
        # still for days; the deep frontier is where the work happens and
        # visibly shrinks as razor cells certify.
        print(f"volume: chart {chart}: {float(100*total):.10f}% "
              f"uncertified{delta(f'volume{chart}', float(total))}; "
              f"deep frontier (depth>=4): {deep_cells} cells, "
              f"{float(deep):.6e}"
              f"{delta(f'deepvol{chart}', float(deep))} "
              f"(checkpoint {age_min:.0f}m old)")


def local_verification_status():
    log = ART / "verify-locals-current.log"
    if not log.exists():
        print("local verification: no live log (verify-locals-current.log)")
        return
    lines = [l for l in log.read_text().splitlines() if l.strip()]
    tables_ok = [l for l in lines if l.startswith("TABLE") and "OK" in l]
    failed = [l for l in lines if "FAILED" in l]
    last_header = max((i for i, l in enumerate(lines)
                       if l.startswith("=== table")), default=0)
    progress = [l for l in lines[last_header:]
                if re.match(r"local \d+: \d+/", l)]
    current = [l for l in lines if l.startswith("=== table")]
    print("local verification: table 0 OK (verified 2026-07-27); "
          + "; ".join(l.strip("= ") for l in current[-1:]) or "")
    for l in tables_ok:
        print(f"  {l}")
    if failed:
        print("  *** " + "; ".join(failed) + " ***")
    if progress:
        print(f"  progress: {progress[-1]}")


def system_status():
    ps = subprocess.run(["ps", "-eo", "comm,pcpu"], capture_output=True,
                        text=True).stdout
    searches = sum(1 for l in ps.splitlines() if "python3" in l
                   and float(l.split()[-1]) > 20)
    # ps truncates comm to 15 chars ("checkNopert76Lo")
    checker = sum(1 for l in ps.splitlines()
                  if "checkNopert76" in l and float(l.split()[-1]) > 50)
    free = subprocess.run(["free", "-g"], capture_output=True,
                          text=True).stdout.splitlines()[1].split()
    print(f"system: ~{searches} busy python workers, "
          f"checker {'RUNNING' if checker else 'not running'}, "
          f"mem {free[6]}G available")


def deep_autopsy():
    path = ART / "chart0.json"
    if not path.exists():
        print("no chart0.json")
        return
    size = path.stat().st_size
    window = 32 << 20
    with open(path, "rb") as f:
        f.seek(max(0, size - window))
        blob = f.read().decode(errors="replace")
    i = blob.rfind('"pending": [')
    j = blob.rfind('], "pending_candidates_omitted"')
    if i < 0 or j < 0 or j < i:
        print("pending array not found in checkpoint tail "
              "(grew past window? checkpoint mid-write?)")
        return
    arr = json.loads(blob[i + len('"pending": '):j + 1])
    print(f"chart-0 pending autopsy: {len(arr)} cells")
    depths = Counter()
    cents = []
    for e in arr:
        tri, vdepth = e[4], e[5]
        depths[vdepth] += 1
        cents.append(tuple(round(sum(float(Q(v[k])) for v in tri) / 3, 2)
                           for k in range(3)))
    print(f"  view-depth histogram: {dict(sorted(depths.items()))}")
    deep = sum(v for k, v in depths.items() if k >= 16)
    print(f"  cells at depth >= 16: {deep}"
          + ("   <-- WATCH: deep pending cells, passage-candidate "
             "signature if they persist" if deep else "  (healthy)"))
    print("  top view clusters (0.01 grid):")
    for k, v in Counter(cents).most_common(8):
        print(f"    {k}: {v}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--deep", action="store_true",
                        help="also autopsy chart-0 pending cells")
    args = parser.parse_args()

    prev = {}
    if SNAPSHOT.exists():
        try:
            prev = json.loads(SNAPSHOT.read_text())
        except json.JSONDecodeError:
            pass
    now = time.time()
    if "time" in prev:
        print(f"[rates vs snapshot {(now - prev['time']) / 3600:.1f}h ago]")

    chart_status(prev, now)
    volume_status(prev, now)
    local_verification_status()
    system_status()
    if args.deep:
        deep_autopsy()

    prev["time"] = now
    SNAPSHOT.write_text(json.dumps(prev))

    print("\nendgame once charts 0+1 complete:")
    print("  python3 scripts/nopert214_emit_packed_global.py "
          ".artifacts/nopert76/chart0.json .artifacts/nopert76/chart0.pack")
    print("  python3 scripts/nopert214_emit_packed_global.py "
          ".artifacts/nopert76/chart1.json .artifacts/nopert76/chart1.pack")
    print("  lake exe constructNopert76 .artifacts/nopert76")


if __name__ == "__main__":
    main()
