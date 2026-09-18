#!/usr/bin/env bash
set -euo pipefail

# Match the actual module, rather than deriving a capitalization from the
# package name. Pin both independent verification tools.
task_checker_dir=".lake/checkers"
mkdir -p "$task_checker_dir"
if [ ! -d "$task_checker_dir/export/.git" ]; then
  git clone https://github.com/leanprover/lean4export.git "$task_checker_dir/export"
fi
git -C "$task_checker_dir/export" checkout bd93e5ed12fbeea19f39ec3ead659c293b2b8a95
cp lean-toolchain "$task_checker_dir/export/lean-toolchain"
(cd "$task_checker_dir/export" && lake build)

if [ ! -d "$task_checker_dir/nanoda/.git" ]; then
  git clone https://github.com/ammkrn/nanoda_lib.git "$task_checker_dir/nanoda"
fi
git -C "$task_checker_dir/nanoda" checkout e5438ac0a85a036b6dfe093aa457bc3448498014
cargo build --release --locked --manifest-path "$task_checker_dir/nanoda/Cargo.toml"

lake env "$task_checker_dir/export/.lake/build/bin/lean4export" JSP628Full -- \
  JSP628.join_matching_avoids JSP628.construction_avoids JSP628.construction_edges JSP628.construction_spec JSP628.critical_arithmetic JSP628.threshold_sharpness JSP628Full.original_resolution JSP628Full.predicate_iff JSP628Full.critical_extremal_strict JSP628Full.stabilizingThreshold_spec JSP628Full.every_threshold_lower JSP628Full.stabilization_bounds String.mk Char.ofNat \
  > "$task_checker_dir/export.txt"
cat > "$task_checker_dir/config.json" <<'JSON'
{
  "export_file_path": ".lake/checkers/export.txt",
  "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
JSON
"$task_checker_dir/nanoda/target/release/nanoda_bin" "$task_checker_dir/config.json"

# Exports all selected theorems and full transitive proof dependencies.
