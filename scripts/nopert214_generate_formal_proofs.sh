#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repo_root"

artifact_dir=${1:-.artifacts/nopert214}
if [[ "$artifact_dir" != /* ]]; then
  artifact_dir="$repo_root/$artifact_dir"
fi
source_dir="$repo_root/Noperthedron/Nopert214"

local_inputs=(
  local-view-r10-child0.json
  local-view-r10-child1.json
  local-view-r10-child2.json
  local-view-r10-child3.json
)
chart_inputs=(
  correlated-tight-chart0.json
  fundamental-tight-chart1.json
  fundamental-tight-chart2.json
)

for input in "${local_inputs[@]}" "${chart_inputs[@]}"; do
  jq -e '.complete == true and (.failures | length) == 0 and
    (.rows | all(. != null))' "$artifact_dir/$input" >/dev/null
done

for index in 0 1 2 3; do
  kernel_namespace="GeneratedLocalView${index}SparseKernel"
  python3 scripts/nopert214_emit_split_kernel_local_view_lean.py \
    "$artifact_dir/${local_inputs[$index]}" \
    "$source_dir/${kernel_namespace}.lean" \
    --table-index "$index" --namespace "$kernel_namespace" \
    --data-chunk-size 64 --proof-part-size 32

  native_namespace="GeneratedLocalView${index}Native"
  python3 scripts/nopert214_emit_packed_local_view_lean.py \
    "$artifact_dir/${local_inputs[$index]}" \
    "$source_dir/${native_namespace}.lean" \
    --table-index "$index" --namespace "$native_namespace" \
    --proof-part-size 256
done

python3 scripts/nopert214_emit_final_aggregators.py "$source_dir"

for chart in 0 1 2; do
  python3 scripts/nopert214_emit_lean.py \
    "$artifact_dir/${chart_inputs[$chart]}" \
    "$source_dir/GeneratedChart${chart}Native.lean" \
    --namespace "GeneratedChart${chart}Native" \
    --shared-local-view-native

  python3 scripts/nopert214_emit_split_kernel_global_lean.py \
    "$artifact_dir/${chart_inputs[$chart]}" \
    "$source_dir/GeneratedChart${chart}.lean" \
    --namespace "GeneratedChart${chart}" \
    --data-chunk-size 64 --interval-chunk-size 16 \
    --kernel-range-size 32 --proof-part-size 256
done

echo "generated native_decide and split kernel proof sources under $source_dir"
