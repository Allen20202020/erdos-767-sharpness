# JSP-000628 / Erdős 767: threshold sharpness

This package formalizes **Construction 3.3 with a = k and Remark 3.4** of
Xiaozheng Chen and Bo Ning, *On Erdős Problem 767: Cycles with Chords*,
[arXiv:2609.15330v1](https://arxiv.org/html/2609.15330v1), 14 September 2026.
It is submitted for review of the **formalization contribution only**.

For every integer k ≥ 2, put n = ceil((5k+1)/2) − 1. We prove the existence
of an n-vertex simple graph with no cycle containing k distinct chords
incident to one vertex, and with exactly

    (k+1)(n−k−1) + 1

edges. Consequently the equality g_k(n) = (k+1)(n−k−1) cannot start at a
smaller threshold than the paper's ceil((5k+1)/2). The proof is uniform in k,
and the constructed graphs are transported to the standard labelled type
`Fin n`.

**Scope:** this completes the paper's sharpness argument and its underlying
matching-join construction. It does not formalize the paper's upper bound,
full extremal formula, nearly regular construction, or all values of a in
Construction 3.3. It does not claim a new mathematical solution.

## Reproduce

Install [elan](https://lean-lang.org/install/), then from this directory:

```sh
lake exe cache get
python3 verify.py
```

Lean 4.34.0 and Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435` are pinned. The complete dependency
manifest is included. The verifier builds with warnings treated as errors,
checks the expanded original statement, checks all six specified axiom
closures against `propext`, `Classical.choice`, and `Quot.sound`, and runs
`leanchecker --fresh --verbose JSP628.Sharpness`.

The GitHub workflow additionally requests an audit of every declaration in
the JSP628 namespace and the independent Rust type checker
[NaNoda](https://github.com/ammkrn/nanoda_lib), with sorry disallowed. See the
actual workflow run for its result; merely configuring a check is not
evidence that it passed.

## Proof and evidence

- [Lean source](JSP628/Sharpness.lean)
- [Expanded statement and edge-count bridge](Audit.lean)
- [Mathematical argument and statement correspondence](STATEMENT.md)
- [Prior work, licensing and attribution](PRIOR_ART.md)
- [Verification records](verification/summary.json)

The submitted work was developed with OpenAI Codex assistance. The submitting
account has a direct interest in recognition of this contribution. Proposed
formalizer identity is `RECIPIENT-JSP000628-A`, pending authorized confirmation.
Award eligibility, allocation within the formalization share, mathematical
human review and organizer-designated verification remain pending. No award,
payment entitlement, worldwide priority, or first-formalization claim is made.
