/-
Copyright 2026 Allen20202020.
Released under the Apache 2.0 license.

Formalization of Chen--Ning, arXiv:2609.15330v1, Construction 3.3 (a = k)
and Remark 3.4. Mathematical credit belongs to Xiaozheng Chen and Bo Ning.
Developed with OpenAI Codex assistance.

The forbidden predicate and selected-neighbour argument are adapted from
plby/lean-proofs, commit 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos767.lean, Apache 2.0, copyright 2026
The Lean-Proofs Authors. The independent-right-side argument and matching
construction below generalize that source's bipartite lower construction.
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

open Finset SimpleGraph
open scoped SimpleGraph

namespace JSP628

noncomputable section

/-- Exactly the existing Erdős 767 predicate, with Mathlib cycles and chords. -/
def HasCycleWithKIncidentChords {V : Type*} (k : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧
    ∃ f : Fin k → V, Function.Injective f ∧ ∀ i, c.IsChord s(v, f i)

section Neighbours
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {v : V}

/-- The two rim neighbours together with all selected chord endpoints. -/
def selected {k : ℕ} (c : G.Walk v v) (f : Fin k → V) : Finset V :=
  {c.snd, c.penultimate} ∪ univ.image f

lemma selected_card {k : ℕ} {c : G.Walk v v} (hc : c.IsCycle)
    {f : Fin k → V} (hf : Function.Injective f)
    (hch : ∀ i, c.IsChord s(v, f i)) : (selected c f).card = k + 2 := by
  have hd : Disjoint ({c.snd, c.penultimate} : Finset V) (univ.image f) := by
    rw [Finset.disjoint_left]
    intro x hx hi
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hi
    have hn := (Walk.isChord_sym2Mk.mp (hch i)).2.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · exact hn (by simpa only [h] using c.mk_start_snd_mem_edges hc.not_nil)
    · exact hn (by simpa only [h, Sym2.eq_swap] using
        c.mk_penultimate_end_mem_edges hc.not_nil)
  rw [selected, card_union_of_disjoint hd, card_image_of_injective _ hf]
  simp [hc.snd_ne_penultimate]
  omega

lemma selected_adj {k : ℕ} {c : G.Walk v v} (hc : c.IsCycle)
    {f : Fin k → V} (hch : ∀ i, c.IsChord s(v, f i))
    {x : V} (hx : x ∈ selected c f) : G.Adj v x := by
  rcases Finset.mem_union.mp hx with hx | hx
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact c.adj_snd hc.not_nil
    · exact (c.adj_penultimate hc.not_nil).symm
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (Walk.isChord_sym2Mk.mp (hch i)).1

lemma selected_mem_cycle {k : ℕ} {c : G.Walk v v} (hc : c.IsCycle)
    {f : Fin k → V} (hch : ∀ i, c.IsChord s(v, f i))
    {x : V} (hx : x ∈ selected c f) : x ∈ c.support.dropLast.toFinset := by
  rw [List.mem_toFinset]
  rcases Finset.mem_union.mp hx with hx | hx
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact c.tail_support_perm_dropLast_support.mem_iff.mp
        (c.snd_mem_tail_support hc.not_nil)
    · exact c.penultimate_mem_dropLast_support hc.not_nil
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    have hi := Walk.isChord_sym2Mk.mp (hch i)
    apply List.mem_dropLast_of_mem_of_ne_getLast hi.2.2.2
    simpa only [c.getLast_support] using hi.1.ne'
end Neighbours

section JoinBound
variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : SimpleGraph (L ⊕ R)}

omit [DecidableEq L] [DecidableEq R] in
lemma card_univ_left :
    (univ.filter fun x : L ⊕ R => x.isLeft).card = Fintype.card L := by
  let e : L ↪ L ⊕ R := ⟨Sum.inl, Sum.inl_injective⟩
  rw [show (univ.filter fun x : L ⊕ R => x.isLeft) = univ.map e by
    ext x
    cases x <;> simp [e]]
  simp

omit [Fintype L] [Fintype R] in
/-- On a simple cycle an independent right side has at most as many vertices
as the left side, even when there are edges within the left side. -/
lemma cycle_right_le_left
    (hR : ∀ x y : R, ¬G.Adj (.inr x) (.inr y))
    {v : L ⊕ R} {c : G.Walk v v} (hc : c.IsCycle) :
    (c.support.dropLast.toFinset.filter fun x => x.isRight).card ≤
      (c.support.dropLast.toFinset.filter fun x => x.isLeft).card := by
  simp only [hc.nodup_dropLast_support.card_eq_countP, Bool.decide_coe]
  calc
    c.support.dropLast.countP Sum.isRight = c.darts.countP (fun d => d.fst.isRight) := by
      rw [← c.map_fst_darts, List.countP_map]
      rfl
    _ ≤ c.darts.countP (fun d => d.snd.isLeft) := by
      apply List.countP_mono_left
      intro d _ hd
      cases hfst : d.fst with
      | inl x => simp [hfst] at hd
      | inr x =>
        cases hsnd : d.snd with
        | inl y => simp
        | inr y => exact (hR x y (by simpa [hfst, hsnd] using d.adj)).elim
    _ = c.support.tail.countP Sum.isLeft := by
      rw [← c.map_snd_darts, List.countP_map]
      rfl
    _ = c.support.dropLast.countP Sum.isLeft :=
      c.tail_support_perm_dropLast_support.countP_eq _

/-- Joining an independent side to a k-vertex side of maximum internal
degree one cannot produce k incident chords on a cycle. -/
theorem join_matching_avoids
    (hR : ∀ x y : R, ¬G.Adj (.inr x) (.inr y))
    (hL : ∀ x y z : L, G.Adj (.inl x) (.inl y) →
      G.Adj (.inl x) (.inl z) → y = z) :
    ¬HasCycleWithKIncidentChords (Fintype.card L) G := by
  rintro ⟨v, c, hc, f, hf, hch⟩
  let S := selected c f
  have hcard : S.card = Fintype.card L + 2 := selected_card hc hf hch
  have hleft : (S.filter fun x => x.isLeft).card ≤ Fintype.card L := by
    rw [← card_univ_left (R := R)]
    exact card_le_card (by intro x hx; simp_all)
  have hsplit : (S.filter fun x => x.isLeft).card +
      (S.filter fun x => x.isRight).card = S.card := by
    have hre : (S.filter fun x => x.isRight) =
        S.filter (fun x => ¬x.isLeft = true) := by
      ext x
      cases x <;> simp
    rw [hre]
    exact Finset.card_filter_add_card_filter_not _

  cases v with
  | inr v =>
    have hrzero : (S.filter fun x => x.isRight) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have ha := selected_adj hc hch (Finset.mem_filter.mp hx).1
      cases x with
      | inl x => simp at hx
      | inr x => exact hR v x ha
    simp only [hrzero, card_empty, add_zero] at hsplit
    omega
  | inl v =>
    have hlone : (S.filter fun x => x.isLeft).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      have hax := selected_adj hc hch (Finset.mem_filter.mp hx).1
      have hay := selected_adj hc hch (Finset.mem_filter.mp hy).1
      cases x with
      | inr x => simp at hx
      | inl x =>
        cases y with
        | inr y => simp at hy
        | inl y => exact congrArg Sum.inl (hL v x y hax hay)
    have hrbound : (S.filter fun x => x.isRight).card ≤ Fintype.card L := by
      have hsub : S.filter (fun x => x.isRight) ⊆
          c.support.dropLast.toFinset.filter (fun x => x.isRight) := by
        intro x hx
        exact mem_filter.mpr ⟨selected_mem_cycle hc hch (mem_filter.mp hx).1,
          (mem_filter.mp hx).2⟩
      apply le_trans (card_le_card hsub)
      apply le_trans (cycle_right_le_left hR hc)
      rw [← card_univ_left (R := R)]
      exact card_le_card (by intro x hx; simp_all)
    omega
end JoinBound

/-- k vertices, grouped in pairs with at most one unmatched vertex. -/
abbrev Left (k : ℕ) := (Fin (k / 2) × Bool) ⊕ Fin (k % 2)
abbrev Vertex (k m : ℕ) := Left k ⊕ Fin m

def matchingEdges (k m : ℕ) : Finset (Sym2 (Vertex k m)) :=
  univ.image fun i : Fin (k / 2) =>
    s(Sum.inl (Sum.inl (i, false)), Sum.inl (Sum.inl (i, true)))

def construction (k m : ℕ) : SimpleGraph (Vertex k m) :=
  completeBipartiteGraph (Left k) (Fin m) ⊔ fromEdgeSet (matchingEdges k m : Set (Sym2 (Vertex k m)))

lemma card_left (k : ℕ) : Fintype.card (Left k) = k := by
  simp [Left, Fintype.card_sum, Fintype.card_prod]
  omega

lemma construction_adj (k m : ℕ) (x y : Vertex k m) :
    (construction k m).Adj x y ↔
      (completeBipartiteGraph (Left k) (Fin m)).Adj x y ∨
      ∃ i : Fin (k / 2),
        (x = .inl (.inl (i, false)) ∧ y = .inl (.inl (i, true))) ∨
        (x = .inl (.inl (i, true)) ∧ y = .inl (.inl (i, false))) := by
  simp only [construction, sup_adj, fromEdgeSet_adj, Finset.mem_coe, matchingEdges,
    mem_image, mem_univ, true_and, Sym2.eq_iff]
  constructor
  · rintro (h | ⟨⟨i, hi⟩, _⟩)
    · exact Or.inl h
    · exact Or.inr ⟨i, by rcases hi with h | h <;> simp_all⟩
  · rintro (h | ⟨i, hi⟩)
    · exact Or.inl h
    · right
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem construction_avoids (k m : ℕ) :
    ¬HasCycleWithKIncidentChords k (construction k m) := by
  have h : ¬HasCycleWithKIncidentChords (Fintype.card (Left k)) (construction k m) := by
    apply join_matching_avoids
    · intro x y
      simp [construction_adj, completeBipartiteGraph_adj]
    · intro x y z hy hz
      simp only [construction_adj, completeBipartiteGraph_adj,
        Sum.isLeft_inl, Sum.isRight_inl, Bool.false_eq_true, and_false,
        false_and, or_self, false_or, Sum.inl.injEq] at hy hz
      obtain ⟨i, hi⟩ := hy
      obtain ⟨j, hj⟩ := hz
      rcases hi with ⟨hx, rfl⟩ | ⟨hx, rfl⟩ <;>
        rcases hj with ⟨hx', rfl⟩ | ⟨hx', rfl⟩ <;> simp_all
  simpa only [card_left] using h

lemma matching_card (k m : ℕ) : (matchingEdges k m).card = k / 2 := by
  rw [matchingEdges, card_image_of_injective]
  · simp
  · intro i j h
    simp only [Sym2.eq_iff, Sum.inl.injEq, Prod.mk.injEq,
      Bool.false_eq_true, and_false, false_and, or_false] at h
    exact h.1.1

lemma matching_edgeFinset (k m : ℕ) :
    (fromEdgeSet (matchingEdges k m : Set (Sym2 (Vertex k m)))).edgeFinset = matchingEdges k m := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [mem_edgeFinset]
    constructor
    · exact And.left
    · intro h
      refine ⟨h, ?_⟩
      obtain ⟨i, _, hi⟩ := mem_image.mp h
      simp only [Sym2.eq_iff] at hi
      rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem construction_edges (k m : ℕ) :
    (construction k m).edgeSet.ncard = k * m + k / 2 := by
  classical
  have hm : (fromEdgeSet (matchingEdges k m : Set (Sym2 (Vertex k m)))).edgeSet =
      (matchingEdges k m : Set (Sym2 (Vertex k m))) := by
    rw [← coe_edgeFinset, matching_edgeFinset]
  have hd : Disjoint (completeBipartiteGraph (Left k) (Fin m)).edgeSet
      (matchingEdges k m : Set (Sym2 (Vertex k m))) := by
    rw [Set.disjoint_left]
    intro e he hm
    obtain ⟨i, _, rfl⟩ := mem_image.mp hm
    simp [completeBipartiteGraph_adj] at he
  rw [construction, edgeSet_sup, hm, Set.ncard_union_eq hd,
    Set.ncard_coe_finset, matching_card]
  have h := encard_edgeSet_completeBipartiteGraph (W₁ := Left k) (W₂ := Fin m)
  rw [ENat.card_eq_coe_fintype_card, ENat.card_eq_coe_fintype_card,
    card_left, Fintype.card_fin] at h
  have h' := congrArg ENat.toNat h
  have hcard : (completeBipartiteGraph (Left k) (Fin m)).edgeSet.ncard = k * m := by
    simpa only [Set.ncard_def, ENat.toNat_mul, ENat.toNat_natCast] using h'
  rw [hcard]

/-- A uniform construction, not a finite computational example. -/
theorem construction_spec (k m : ℕ) :
    Fintype.card (Vertex k m) = k + m ∧
    ¬HasCycleWithKIncidentChords k (construction k m) ∧
    (construction k m).edgeSet.ncard = k * m + k / 2 := by
  refine ⟨?_, construction_avoids k m, construction_edges k m⟩
  change Fintype.card (Left k ⊕ Fin m) = k + m
  rw [Fintype.card_sum, card_left, Fintype.card_fin]

/-- One vertex below the Chen--Ning threshold ceil((5k+1)/2). -/
def criticalOrder (k : ℕ) := (5 * k + 2) / 2 - 1

lemma critical_arithmetic {k : ℕ} (hk : 2 ≤ k) :
    k ≤ criticalOrder k ∧
    k * (criticalOrder k - k) + k / 2 =
      (k + 1) * (criticalOrder k - k - 1) + 1 := by
  have hmod := Nat.mod_lt k (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div k 2
  have hformula : criticalOrder k = 2 * k + k / 2 := by
    unfold criticalOrder
    omega
  rw [hformula]
  constructor
  · omega
  · have hsub : 2 * k + k / 2 - k = k + k / 2 := by omega
    rw [hsub]
    have hsub1 : k + k / 2 - 1 + 1 = k + k / 2 := by omega
    nlinarith

/-- Transport of the literal Mathlib chord predicate along a graph embedding.
Adapted from the Apache-2.0 source credited in the file header. -/
lemma chord_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ↪g H) {a b : V} {c : G.Walk a b} {e : Sym2 V}
    (he : c.IsChord e) : (c.map φ.toHom).IsChord (e.map φ) := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [Walk.isChord_sym2Mk] at he
    change (c.map φ.toHom).IsChord s(φ x, φ y)
    rw [Walk.isChord_sym2Mk]
    rcases he with ⟨hxy, hnot, hx, hy⟩
    refine ⟨φ.toHom.map_adj hxy, ?_, ?_, ?_⟩
    · rw [Walk.edges_map]
      intro hmem
      obtain ⟨e, hec, heq⟩ := List.mem_map.mp hmem
      have heeq : e = s(x, y) := (Sym2.map.injective φ.injective) heq
      exact hnot (heeq ▸ hec)
    · simp only [Walk.support_map, List.mem_map]
      exact ⟨x, hx, rfl⟩
    · simp only [Walk.support_map, List.mem_map]
      exact ⟨y, hy, rfl⟩

lemma has_cycle_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ↪g H) {k : ℕ} (hG : HasCycleWithKIncidentChords k G) :
    HasCycleWithKIncidentChords k H := by
  rcases hG with ⟨v, c, hc, f, hf, hch⟩
  refine ⟨φ v, c.map φ.toHom, hc.map φ.injective,
    (fun i => φ (f i)), φ.injective.comp hf, ?_⟩
  intro i
  simpa only [Sym2.map_mk] using chord_map φ (hch i)

/-- Complete formalization of Chen--Ning Remark 3.4: for every k ≥ 2,
at one vertex below ceil((5k+1)/2), the predicted Jiang edge count can be
exceeded by one without any cycle carrying k incident chords. -/
theorem threshold_sharpness (k : ℕ) (hk : 2 ≤ k) :
    ∃ G : SimpleGraph (Fin (criticalOrder k)),
      ¬HasCycleWithKIncidentChords k G ∧
      G.edgeSet.ncard = (k + 1) * (criticalOrder k - k - 1) + 1 := by
  have ⟨hkn, hcalc⟩ := critical_arithmetic hk
  let m := criticalOrder k - k
  let H := construction k m
  have hverts : Fintype.card (Vertex k m) = criticalOrder k := by
    rw [(construction_spec k m).1]
    exact Nat.add_sub_of_le hkn
  let e : Vertex k m ≃ Fin (criticalOrder k) := Fintype.equivFinOfCardEq hverts
  let φ := SimpleGraph.Iso.map e H
  refine ⟨H.map e, ?_, ?_⟩
  · intro h
    exact construction_avoids k m (has_cycle_map φ.symm.toEmbedding h)
  · calc
      (H.map e).edgeSet.ncard = H.edgeSet.ncard :=
        Set.ncard_congr' φ.mapEdgeSet.symm
      _ = k * m + k / 2 := construction_edges k m
      _ = (k + 1) * (criticalOrder k - k - 1) + 1 := hcalc

end
end JSP628
