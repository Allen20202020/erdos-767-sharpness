import JSP628

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
