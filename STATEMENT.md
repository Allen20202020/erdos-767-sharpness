# Statement and proof correspondence

## Original result

Chen and Ning, [arXiv:2609.15330v1](https://arxiv.org/html/2609.15330v1),
Construction 3.3 and Remark 3.4, construct a graph with an a-vertex part X,
an independent (n−a)-vertex part Y, all cross edges, and a specified
nearly regular graph within X. At a = k, the internal graph is a matching
with floor(k/2) edges. Taking n = ceil((5k+1)/2)−1 gives exactly one edge
more than (k+1)(n−k−1), without a cycle having k incident chords.

## Literal formal statement

`JSP628.threshold_sharpness` quantifies over every natural k with 2 ≤ k:

```lean
∃ G : SimpleGraph (Fin (criticalOrder k)),
  ¬HasCycleWithKIncidentChords k G ∧
  G.edgeSet.ncard = (k + 1) * (criticalOrder k - k - 1) + 1
```

`criticalOrder k = (5*k+2)/2−1` uses natural division, and equals
ceil((5k+1)/2)−1. `critical_arithmetic` proves n ≥ k and the relevant exact
integer identity; its proof also establishes n = 2k+floor(k/2). With k ≥ 2,
this n is at least k+2, as required by the original extremal problem.

`HasCycleWithKIncidentChords` is the existing Erdős 767 predicate: it uses
Mathlib's `Walk.IsCycle`, an injective map from `Fin k` selecting distinct
endpoints, and the literal Mathlib `Walk.IsChord` predicate. Rim edges are
excluded by that predicate. `Audit.lean` expands all of this in a typed
restatement, so the result is not proved by assuming a bespoke surrogate.
It also proves that `edgeSet.ncard` equals `edgeFinset.card` whenever the
edge set is given a finite enumeration. Every graph in the main theorem
is on `Fin n`, so there is no infinite-set cardinality ambiguity.

## Complete argument implemented in Lean

1. The left part has floor(k/2) disjoint pairs and k mod 2 unmatched vertices.
   Its cardinality is exactly k. The right part has m vertices. Add every
   cross edge and one edge inside each left pair.
2. In any simple cycle, the right vertices number at most the left vertices:
   every directed cycle edge starting on the right ends on the left. Counts
   of edge starts and ends match counts of cycle vertices, excluding the
   repeated starting vertex. This uses actual walk darts and cycle support.
3. A forbidden cycle with k incident chords has k+2 distinct neighbours of
   its center on the cycle: the k chord endpoints and its two rim neighbours.
   The rim neighbours are distinct and disjoint from the chord endpoints.
4. If the center is on the right, all these neighbours lie among k left
   vertices. If the center is on the left, at most one neighbour lies on
   the left; at most k right vertices lie on the cycle by step 2. Both
   cases contradict the k+2 distinct selected neighbours.
5. Cross edges and matching edges are disjoint. They number km and
   floor(k/2), respectively. Thus the graph has km+floor(k/2) edges.
6. Set m = n−k at the critical order. Natural-number arithmetic proves
   km+floor(k/2) = (k+1)(n−k−1)+1. A graph isomorphism relabels the vertices
   by `Fin n`; cycles, chords, distinct endpoints, and edge counts are
   transported without adding hypotheses.

The generic structural theorem `join_matching_avoids` proves step 4 for
any finite graph whose right side is independent and whose left internal
degree is at most one. The theorem `construction_spec` proves all three
conditions of the actual construction for every k and m, not just at the
critical order. No computational sampling is used as a replacement for
any universal statement.
