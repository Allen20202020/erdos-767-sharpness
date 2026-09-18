/-
Copyright 2026 Allen20202020. Released under Apache 2.0.
Developed with OpenAI Codex assistance. The complete original forcing and
extremal formula are prior work by Codex / GPT-5.6 Sol, formalizing Tao Jiang.
The critical-order construction is our separately attributed Chen--Ning formalization.
-/
import ErdosProblems.Erdos767
import JSP628Full.Sharpness

namespace JSP628Full
open SimpleGraph

/-- The original question: the exact extremal formula eventually holds. -/
theorem original_resolution (k : ℕ) (hk : 0 < k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Erdos767.chordCycleExtremalNumber k n = (k + 1) * n - (k + 1) ^ 2 :=
  ⟨3 * k + 3, fun n hn => Erdos767.erdos_767 k n hk hn⟩

/-- Agreement of the actual Mathlib cycle/chord predicates in both packages. -/
theorem predicate_iff {V : Type*} (k : ℕ) (G : SimpleGraph V) :
    JSP628.HasCycleWithKIncidentChords k G ↔
      Erdos767.HasCycleWithKIncidentChords k G := Iff.rfl

/-- The new critical-order graph gives a strict lower bound for the genuine
extremal number, not merely an isolated graph certificate. -/
theorem critical_extremal_strict (k : ℕ) (hk : 2 ≤ k) :
    (k + 1) * JSP628.criticalOrder k - (k + 1) ^ 2 <
      Erdos767.chordCycleExtremalNumber k (JSP628.criticalOrder k) := by
  classical
  obtain ⟨G, havoid, he⟩ := JSP628.threshold_sharpness k hk
  have havoid' : Erdos767.AvoidsCycleWithKIncidentChords k G :=
    fun h => havoid ((predicate_iff k G).mpr h)
  have hbound := Erdos767.card_edgeFinset_le_chordCycleExtremalNumber havoid'
  have hc : G.edgeSet.ncard = G.edgeFinset.card :=
    Set.ncard_eq_toFinset_card' G.edgeSet
  rw [hc] at he
  have harith : (k + 1) * JSP628.criticalOrder k - (k + 1) ^ 2 =
      (k + 1) * (JSP628.criticalOrder k - k - 1) := by
    rw [pow_two, ← Nat.mul_sub_left_distrib]
    congr 1
  rw [harith]
  omega

/-- A genuine stabilization threshold quantifies over every larger order. -/
def IsStabilizingThreshold (k N : ℕ) : Prop :=
  ∀ n : ℕ, N ≤ n →
    Erdos767.chordCycleExtremalNumber k n = (k + 1) * n - (k + 1) ^ 2

/-- The least order after which the exact formula always holds. -/
noncomputable def stabilizingThreshold (k : ℕ) : ℕ :=
  sInf {N : ℕ | IsStabilizingThreshold k N}

theorem stabilizingThreshold_spec (k : ℕ) (hk : 0 < k) :
    IsStabilizingThreshold k (stabilizingThreshold k) :=
  csInf_mem (original_resolution k hk)

/-- The matching-join construction bounds every possible stabilization threshold. -/
theorem every_threshold_lower (k N : ℕ) (hk : 2 ≤ k)
    (hN : IsStabilizingThreshold k N) : JSP628.criticalOrder k + 1 ≤ N := by
  by_contra h
  have heq := hN (JSP628.criticalOrder k) (by omega)
  have hstrict := critical_extremal_strict k hk
  rw [heq] at hstrict
  exact (Nat.lt_irrefl _) hstrict

/-- Complete original resolution plus nontrivial bounds on the least threshold.
The lower endpoint is ceil((5k+1)/2); the upper endpoint is Jiang's 3k+3. -/
theorem stabilization_bounds (k : ℕ) (hk : 2 ≤ k) :
    JSP628.criticalOrder k + 1 ≤ stabilizingThreshold k ∧
      stabilizingThreshold k ≤ 3 * k + 3 := by
  constructor
  · exact every_threshold_lower k _ hk (stabilizingThreshold_spec k (by omega))
  · exact csInf_le' (fun n hn => Erdos767.erdos_767 k n (by omega) hn)

end JSP628Full
