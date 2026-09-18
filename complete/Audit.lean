import JSP628Full

open scoped SimpleGraph

-- Expand the entry predicate in the original problem's literal vocabulary.
example (k : ℕ) (hk : 2 ≤ k) :
    ∃ G : SimpleGraph (Fin ((5 * k + 2) / 2 - 1)),
      (¬∃ (v : Fin ((5 * k + 2) / 2 - 1)) (c : G.Walk v v), c.IsCycle ∧
        ∃ f : Fin k → Fin ((5 * k + 2) / 2 - 1),
          Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)) ∧
      G.edgeSet.ncard = (k + 1) * (((5 * k + 2) / 2 - 1) - k - 1) + 1 :=
  JSP628.threshold_sharpness k hk

-- Explicitly connect the set-cardinality convention to Mathlib's edgeFinset.
example {V : Type*} (G : SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  exact Set.ncard_eq_toFinset_card' G.edgeSet

#check JSP628.threshold_sharpness
#print axioms JSP628.join_matching_avoids
#print axioms JSP628.construction_avoids
#print axioms JSP628.construction_edges
#print axioms JSP628.construction_spec
#print axioms JSP628.critical_arithmetic
#print axioms JSP628.threshold_sharpness

-- Exact original eventual equality; no added mathematical hypothesis.
example (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Erdos767.chordCycleExtremalNumber k n = (k + 1) * n - (k + 1) ^ 2 :=
  JSP628Full.original_resolution k hk

#print axioms JSP628Full.original_resolution
#print axioms JSP628Full.predicate_iff
#print axioms JSP628Full.critical_extremal_strict
#print axioms JSP628Full.stabilizingThreshold_spec
#print axioms JSP628Full.every_threshold_lower
#print axioms JSP628Full.stabilization_bounds
