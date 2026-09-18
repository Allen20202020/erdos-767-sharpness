# Statement correspondence

The original [problem 767](https://www.erdosproblems.com/767) asks whether, for each positive k, the maximum number of edges in a graph avoiding a cycle with k distinct chords incident to one vertex eventually equals `(k+1)n − (k+1)²`. The imported definition takes the maximum over every labelled simple graph on `Fin n`. The forbidden configuration uses Mathlib `Walk.IsCycle`, `Walk.IsChord` and an injective map selecting distinct chord endpoints. `predicate_iff` proves exact agreement with our construction predicate.

| Component | Declaration in `JSP628Full/Main.lean` |
| --- | --- |
| Complete original eventual extremal equality, all positive k | `original_resolution` |
| Identical forbidden configurations | `predicate_iff` |
| Strict inequality for the genuine extremal number at `criticalOrder k` | `critical_extremal_strict` |
| The least threshold itself works for all subsequent orders | `stabilizingThreshold_spec` |
| Every working threshold exceeds the critical order | `every_threshold_lower` |
| Lower and upper bounds on the least working threshold, every k ≥ 2 | `stabilization_bounds` |

Here `criticalOrder k = (5*k+2)/2 - 1`, with natural-number division. Thus `criticalOrder k+1 = ceil((5k+1)/2)` for k ≥ 2. The original equality covers k=1 as well; the new lower-bound construction is stated for k ≥ 2. There are no extra unproved mathematical assumptions. The sharpness argument is uniform in k, rather than a finite numerical search.

The complete original forcing theorem is prior work, `Erdos767.erdos_767`, giving a sufficient order of `3k+3`. The stronger improved upper threshold from Chen–Ning's 2026 paper is outside this package's proved scope. No claim of having completely formalized that newer paper is made.
