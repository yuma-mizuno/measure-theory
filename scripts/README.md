# Scripts

- `check-katex.mjs` verifies that the KaTeX commands used by the documentation are supported.
- `generate-docs.sh` runs the KaTeX check and then generates the Lebesgue documentation with `lake exe lebesgue-doc`.
- `check-doc-build-clean.sh` removes Lebesgue documentation build artifacts and cached highlighted declaration data, then runs a fresh documentation build without clearing dependency build outputs such as mathlib. If `--output` is not provided, it builds into a temporary directory and deletes that output on success.
