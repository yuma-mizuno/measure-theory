#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

output_dir=""
forwarded_args=()
while (($# > 0)); do
  case "$1" in
    --output)
      if (($# < 2)); then
        echo "error: missing directory after --output" >&2
        exit 1
      fi
      output_dir="$2"
      forwarded_args+=("$1" "$2")
      shift 2
      ;;
    *)
      forwarded_args+=("$1")
      shift
      ;;
  esac
done

temp_output=""
cleanup() {
  local status=$?
  if [[ -n "$temp_output" ]]; then
    if [[ $status -eq 0 ]]; then
      rm -rf "$temp_output"
    else
      printf 'Preserving failed doc output at %s\n' "$temp_output" >&2
    fi
  fi
}
trap cleanup EXIT

if [[ -z "$output_dir" ]]; then
  temp_output="$(mktemp -d "${TMPDIR:-/tmp}/measure-verso-doc-build.XXXXXX")"
  forwarded_args=(--output "$temp_output" "${forwarded_args[@]}")
fi

echo "Cleaning Lebesgue doc build artifacts..."
rm -rf \
  .lake/build/highlighted \
  .lake/build/lebesgue_doc \
  .lake/build/lib/lean/MeasureTheory/Measure/LebesgueDoc \
  .lake/build/ir/MeasureTheory/Measure/LebesgueDoc
rm -f \
  .lake/build/lib/lean/MeasureTheory/Measure/LebesgueDoc.ilean \
  .lake/build/lib/lean/MeasureTheory/Measure/LebesgueDoc.ilean.hash \
  .lake/build/lib/lean/MeasureTheory/Measure/LebesgueDoc.olean \
  .lake/build/lib/lean/MeasureTheory/Measure/LebesgueDoc.olean.hash \
  .lake/build/lib/lean/MeasureTheory/Measure/LebesgueDoc.trace \
  .lake/build/ir/MeasureTheory/Measure/LebesgueDoc.c \
  .lake/build/ir/MeasureTheory/Measure/LebesgueDoc.setup.json

node scripts/check-katex.mjs

echo "Running clean documentation build..."
lake exe lebesgue-doc "${forwarded_args[@]}"

echo "Documentation build completed successfully."
