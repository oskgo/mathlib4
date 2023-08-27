/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Extr

/-!
# Turán graphs and Turán's theorem

This file defines Turán graphs, complete multipartite graphs on given numbers of vertices and parts
with part sizes as even as possible.

## Main declarations

* `SimpleGraph.isoTuranGraph`: Turán's theorem. `turanGraph n r` is the unique graph up to
isomorphism with the maximum number of edges among `n`-vertex graphs without `(r + 1)`-cliques.
-/

namespace SimpleGraph

variable (n r : ℕ) (hr : 0 < r)

/-- The `r`-partite Turán graph on `n` vertices has `Fin n` as its vertex set and an edge between
every pair of vertices with different residues modulo `r`. -/
def turanGraph : SimpleGraph (Fin n) where Adj v w := v % r ≠ w % r

-- def turanGraph' :=
-- completeMultipartiteGraph fun i : Fin r => Fin (n / r + if i < n % r then 1 else 0)

/-- `turanGraph n r` has no `(r + 1)`-cliques. -/
lemma cliqueFree_turanGraph : (turanGraph n r).CliqueFree (r + 1) := fun t => by
  rw [isNClique_iff, and_comm, not_and]
  intro hc
  simp only [IsClique, Set.Pairwise, not_forall, turanGraph]
  have : ∀ k, k ∈ t → k.1 % r ∈ Finset.Ico 0 r := fun _ _ => by simpa using Nat.mod_lt _ hr
  obtain ⟨v, hv, w, hw, hn, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp [hc]) this
  use v, hv, w, hw
  simp_all

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set of `n`-vertex graphs with no `(r + 1)`-cliques. -/
def turanSet : Set (SimpleGraph V) := {H | Fintype.card V = n ∧ H.CliqueFree (r + 1)}

lemma turanGraph_mem_turanSet : turanGraph n r ∈ turanSet n r := by
  rw [turanSet, Fintype.card_fin]
  exact ⟨rfl, cliqueFree_turanGraph n r hr⟩

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `G.IsTuranMaximal n r` indicates that `G` has a maximal number of edges among graphs in
`turanSet n r`. -/
def IsTuranMaximal : Prop := IsMaxOn (Set.ncard ∘ edgeSet) (turanSet n r) G

/-- The graph formed by replacing `t` with a copy of `s`, by changing `t`'s neighbours to match.
The `s-t` edge is removed if present. -/
def replaceVertex (s t : V) : SimpleGraph V where
  Adj := G.Adj \ Sym2.ToRel (G.incidenceSet t) ⊔ Sym2.ToRel {⟦(t, v)⟧ | v ∈ G.neighborSet s \ {t}}
  symm v w := by
    intro h; cases h
    · exact Or.inl (by simpa [adj_comm, Sym2.eq_swap])
    · aesop
  loopless v := by simp only [Set.mem_diff, Pi.sup_apply, Pi.sdiff_apply, SimpleGraph.irrefl,
    Sym2.toRel_prop, Set.mem_setOf_eq, Quotient.eq, Sym2.rel_iff, or_self, exists_eq_right_right,
    le_Prop_eq, sdiff_le_iff, IsEmpty.forall_iff, sup_of_le_right]; tauto

theorem replaceVertex_self (s : V) : G.replaceVertex s s = G := by
  rw [replaceVertex]
  congr!
  ext x y
  rw [incidenceSet]
  simp_all only [mem_neighborSet, SimpleGraph.irrefl, not_false_eq_true, Set.diff_singleton_eq_self,
    Pi.sup_apply, Pi.sdiff_apply, Sym2.toRel_prop, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff,
    Quotient.eq, Sym2.rel_iff, ge_iff_le, le_Prop_eq, forall_exists_index, and_imp, sdiff_le_iff,
    sup_Prop_eq, true_and]
  by_cases ha : Adj G x y
  · simp_all only [true_and, iff_true]
    change ⊤ \ _ ∨ _
    simp only [top_sdiff', hnot_eq_compl, compl_iff_not]
    rw [← imp_iff_not_or]
    intro e
    cases' e with z z
    · use y; rw [z]; simpa
    · use x; rw [z, adj_comm]; simpa
  · simp_all only [false_and, sdiff_self, iff_false]
    change ¬(False ∨ _)
    simp only [false_or, not_exists, not_and]
    intro b hb
    push_neg
    constructor <;> (intro e; contrapose! hb; simpa only [e, hb, adj_comm] using ha)

/-- Clique-freeness is preserved by `replaceVertex`. -/
theorem cliqueFree_of_replaceVertex_cliqueFree (s t : V) (h : G.CliqueFree r) :
    (G.replaceVertex s t).CliqueFree r := by
  contrapose h
  obtain ⟨⟨f, hi⟩, ha⟩ := topEmbeddingOfNotCliqueFree h
  simp only [Function.Embedding.coeFn_mk, top_adj, replaceVertex, incidenceSet,
    mem_neighborSet, Set.mem_diff, Set.mem_singleton_iff, Pi.sup_apply, Pi.sdiff_apply,
    Sym2.toRel_prop, Set.mem_setOf_eq, mem_edgeSet, Sym2.mem_iff, Quotient.eq, Sym2.rel_iff,
    ge_iff_le, le_Prop_eq, forall_exists_index, and_imp, sdiff_le_iff, sup_Prop_eq, ne_eq] at ha
  rw [not_cliqueFree_iff]
  by_cases mt : t ∈ Set.range f
  · obtain ⟨x, hx⟩ := mt
    by_cases ms : s ∈ Set.range f
    · obtain ⟨y, hy⟩ := ms
      by_cases hst : s = t
      · rw [hst, replaceVertex_self, not_cliqueFree_iff] at h
        exact h
      · replace ha := @ha x y
        simp_all only [true_or, and_true, sdiff_self, true_and]
        change False ∨ _ ↔ _ at ha
        have vst : ∀ (v s t : V), (v = s ∨ t = s ∧ v = t) = (v = s) := by simp
        have : ¬x = y := by intro a; simp_all only [not_true]
        simp [vst, this] at ha
    · use ⟨fun v => if v = x then s else f v, ?_⟩
      swap
      · intro a b
        dsimp only
        split_ifs
        · simp_all
        · intro; simp_all
        · intro; simp_all
        · apply hi
      intro a b
      simp only [Function.Embedding.coeFn_mk, top_adj, ne_eq]
      split_ifs with h1 h2 h2
      · simp_all
      · rw [eq_comm] at h1 h2
        subst h1
        simp only [h2, iff_true]
        have := (@ha x b).mpr h2
        simp_all only [Set.mem_range, not_exists, true_or, and_true, sdiff_self, true_and]
        change False ∨ _ at this
        simp only [false_or] at this
        have hv : ∀ (v t : V), (v = f b ∨ t = f b ∧ v = t) = (v = f b) := by simp
        simp only [hv, exists_eq_right] at this
        exact this.1
      · rw [eq_comm] at h2
        subst h2
        simp only [h1, iff_true]
        have := (@ha a x).mpr h1
        simp_all only [Set.mem_range, not_exists, or_true, and_true, sdiff_self, true_and]
        change False ∨ _ at this
        simp only [false_or] at this
        have hv : ∀ (v t : V), (t = f a ∧ v = t ∨ v = f a) = (v = f a) := by simp
        simp only [hv, exists_eq_right] at this
        exact this.1.symm
      · rw [← @ha a b]
        have ha : (t = f a) = False := by
          have := (@hi a x).mt h1
          rw [hx, eq_comm] at this
          simpa
        have hb : (t = f b) = False := by
          have := (@hi b x).mt h2
          rw [hx, eq_comm] at this
          simpa
        simp only [ha, hb, or_self, and_false, false_and, exists_false, or_false]
        change _ ↔ _ \ ⊥
        simp only [sdiff_bot]
  · use ⟨f, hi⟩
    simp_all only [Set.mem_range, not_exists, Function.Embedding.coeFn_mk, top_adj, ne_eq]
    intro a b
    rw [← @ha a b]
    have mta := eq_false (mt a)
    have mtb := eq_false (mt b)
    rw [@eq_comm _ _ t] at mta mtb
    simp only [mta, mtb, or_self, and_false, false_and, exists_false, or_false]
    change _ ↔ _ \ ⊥
    simp only [sdiff_bot]

/-- Membership in `turanSet` is preserved by `replaceVertex`. -/
theorem mem_replaceVertex_of_mem_turanSet (s t : V) (h : G ∈ turanSet n r) :
    (G.replaceVertex s t) ∈ turanSet n r := by
  simp_all [turanSet, cliqueFree_of_replaceVertex_cliqueFree]

lemma one (v w : V) (hm : G ∈ turanSet n r) (ha : ¬G.Adj v w) (hd : G.degree v ≠ G.degree w) :
    ¬G.IsTuranMaximal n r := by
  wlog hg : G.degree w < G.degree v generalizing v w
  · rw [adj_comm] at ha
    exact this w v ha hd.symm (hd.lt_or_lt.resolve_right hg)
  clear hd
  simp only [IsTuranMaximal, isMaxOn_iff, not_forall, Function.comp_apply, not_le]
  use G.replaceVertex v w, G.mem_replaceVertex_of_mem_turanSet n r v w hm
  sorry

variable {G}

/-- **Turán's theorem**. An `n`-vertex graph with no `(r + 1)`-cliques and the maximum number of
edges is isomorphic to `turanGraph n r`. -/
def isoTuranGraph (hmax : G.IsTuranMaximal n r) : G ≃g turanGraph n r := by
  sorry

end SimpleGraph
