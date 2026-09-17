#!/usr/bin/env bash
set -euo pipefail

# Match the actual module, rather than deriving a capitalization from the
# package name. Pin both independent verification tools.
task_checker_dir=".lake/checkers"
mkdir -p "$task_checker_dir"
git clone https://github.com/leanprover/lean4export.git "$task_checker_dir/export"
git -C "$task_checker_dir/export" checkout 6cea97789dc088ea47fcea15692db85685aedac5
cp lean-toolchain "$task_checker_dir/export/lean-toolchain"
(cd "$task_checker_dir/export" && lake build)

git clone https://github.com/ammkrn/nanoda_lib.git "$task_checker_dir/nanoda"
git -C "$task_checker_dir/nanoda" checkout e5438ac0a85a036b6dfe093aa457bc3448498014
cargo build --release --manifest-path "$task_checker_dir/nanoda/Cargo.toml"

lake env "$task_checker_dir/export/.lake/build/bin/lean4export" JSP628 > "$task_checker_dir/export.txt"
cat > "$task_checker_dir/config.json" <<'JSON'
{
  "export_file_path": ".lake/checkers/export.txt",
  "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
  "unpermitted_axiom_hard_error": true,
  "nat_extension": true,
  "string_extension": true,
  "print_success_message": true
}
JSON
"$task_checker_dir/nanoda/target/release/nanoda_bin" "$task_checker_dir/config.json"

# The export includes imported Mathlib declarations; its native compiler axiom
# is allowed here. The separate namespace audit permits ONLY the three core
# axioms for every JSP628 declaration and its full dependency closure.
