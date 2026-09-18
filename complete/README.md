# JSP-000628: complete original resolution and stabilization bounds

This package proves the **complete original [Erdős problem 767](https://www.erdosproblems.com/767)**: for every positive k, the exact extremal formula holds for every sufficiently large order. `JSP628Full.original_resolution` gives the explicit sufficient order `3k+3` by reusing the credited, complete prior formalization of Tao Jiang's theorem. This existing proof is not our new contribution.

The new contribution combines our symbolic Chen–Ning critical-order construction with that actual extremal number. `critical_extremal_strict` proves a strict inequality at the critical order; `stabilization_bounds` proves that the **least eventual stabilization order** lies between `ceil((5k+1)/2)` and `3k+3` for every k ≥ 2. Existence and minimality quantify over every larger order. The graph predicates are proved identical, so the lower bound and the original solution refer to the same problem.

This package does not prove the recent paper's improved upper bound at `ceil((5k+1)/2)`. The least-threshold bounds, the complete original solution, and the sharpness component must not be confused. See [STATEMENT.md](STATEMENT.md) and [ATTRIBUTION.md](ATTRIBUTION.md). Award eligibility and the value of this incremental formalization require organizer review; successful checks are not an award decision.

## Reproduce

From this `complete` directory, with Python 3, Git and elan installed:

```sh
python3 scripts/fetch_upstream.py
lake exe cache get
python3 verify.py
```

Lean v4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` are pinned. The fetch script retrieves exactly 27 upstream modules at commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, checks every SHA-256 hash, and preserves their original attribution. These dependency files are excluded from Git. The verification script builds with warnings treated as errors, checks all twelve selected theorem axiom closures, and performs bundled-kernel replay of the project modules (using cached imported dependencies). The independent NaNoda run separately rechecks the full transitive dependency closures of all selected results. Local records are under [evidence](evidence/).

For verification with a second kernel implementation, install Rust/Cargo and run:

```sh
bash scripts/nanoda.sh
```

Both checker tools are pinned; NaNoda rejects axioms outside `propext`, `Classical.choice`, `Quot.sound`. [GitHub Actions](../.github/workflows/complete-proof.yml) reproduces these checks in a fresh Linux job. Cached dependency artifacts are used; contributor-run verification is not independent human or organizer review.
