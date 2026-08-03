#!/bin/sh
# Resume the two paused Nopert #76 chart searches (paused 2026-07-30).
# Safe to run repeatedly; both searches checkpoint atomically every 1000
# rows. Watch progress with: python3 scripts/nopert76_status.py [--deep]
cd "$(dirname "$0")/.." || exit 1

# gmpy2.mpq instead of Fraction: measured 1.20x (chart0 wave) / 1.28x
# (chart1) end-to-end, checkpoint-format identical, Lean re-verifies rows.
export NOPERT_GMPY2=1

prlimit --as=17179869184 nice -n 10 \
python3 scripts/nopert76_certificate_search.py generate-atlas-projective-table 0 \
  .artifacts/nopert76/chart0.json \
  --max-nodes 2000000 --max-view-depth 22 --min-relative-half-width 1/32768 \
  --checkpoint-every 1000 --checkpoint-min-seconds 900 \
  --restricted-fundamental-root \
  --chart0-origin-tube-radii 1/10000000,1/10000000,1/10000000,1/10000000 \
  --resume --workers 9 >> .artifacts/nopert76/chart0-run10.log 2>&1 &
echo "chart0 resumed (pid $!, log chart0-run10.log)"

prlimit --as=34359738368 nice -n 10 \
python3 scripts/nopert76_certificate_search.py generate-atlas-projective-table 1 \
  .artifacts/nopert76/chart1.json \
  --max-nodes 8000000 --max-view-depth 18 --min-relative-half-width 1/32768 \
  --checkpoint-every 4000 --checkpoint-min-seconds 900 \
  --restricted-fundamental-root \
  --resume --workers 5 >> .artifacts/nopert76/chart1-run7.log 2>&1 &
echo "chart1 resumed (pid $!, log chart1-run7.log)"

echo "endgame after both complete:"
echo "  python3 scripts/nopert214_emit_packed_global.py .artifacts/nopert76/chart0.json .artifacts/nopert76/chart0.pack"
echo "  python3 scripts/nopert214_emit_packed_global.py .artifacts/nopert76/chart1.json .artifacts/nopert76/chart1.pack"
echo "  lake exe constructNopert76 .artifacts/nopert76"
