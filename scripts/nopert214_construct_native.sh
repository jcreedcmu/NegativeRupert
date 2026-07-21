#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

artifact_dir=${1:-.artifacts/nopert214}
if [[ "$artifact_dir" != /* ]]; then
  artifact_dir="$repo_root/$artifact_dir"
fi

pack_local() {
  local index=$1
  local input=$2
  local output="$artifact_dir/local-view${index}.pack"
  python3 scripts/nopert214_emit_packed_local_view_lean.py \
    "$artifact_dir/$input" /dev/null \
    --table-index "$index" --namespace "GeneratedLocalView${index}Native" \
    --raw-output "$output.new" --raw-only
  mv -f "$output.new" "$output"
}

pack_chart() {
  local index=$1
  local input=$2
  local output="$artifact_dir/chart${index}.pack"
  python3 scripts/nopert214_emit_packed_global.py \
    "$artifact_dir/$input" "$output.new"
  mv -f "$output.new" "$output"
}

pack_local 0 local-view-exact-boundary-child0.json
pack_local 1 local-view-r100-child1.json
pack_local 2 local-view-r10-child2.json
pack_local 3 local-view-r10-child3.json

pack_chart 0 correlated-tight-chart0.json
pack_chart 1 correlated-tight-chart1.json
pack_chart 2 correlated-tight-chart2.json

lake build constructNopert214
exec .lake/build/bin/constructNopert214 "$artifact_dir"
