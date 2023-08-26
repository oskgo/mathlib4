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
  · by_cases ms : s ∈ Set.range f
    · sorry
    · sorry
  · use ⟨f, hi⟩
    simp_all
    intro a b
    rw [← @ha a b]
    have mta := eq_false (mt a)
    rw [@eq_comm _ _ t] at mta
    have mtb := eq_false (mt b)
    rw [@eq_comm _ _ t] at mtb
    simp only [mta, mtb, or_self, and_false, false_and, exists_false, or_false]

lemma one (v w : V) (ha : ¬G.Adj v w) (hd : G.degree v ≠ G.degree w) :
    ¬G.IsTuranMaximal n r := by
  wlog hg : G.degree w < G.degree v generalizing v w
  · rw [adj_comm] at ha
    exact this w v ha hd.symm (hd.lt_or_lt.resolve_right hg)
  clear hd
  simp only [IsTuranMaximal, isMaxOn_iff, not_forall, Function.comp_apply, not_le]
  use G.replaceVertex v w
  sorry

variable {G}

/-- **Turán's theorem**. An `n`-vertex graph with no `(r + 1)`-cliques and the maximum number of
edges is isomorphic to `turanGraph n r`. -/
def isoTuranGraph (hmax : G.IsTuranMaximal n r) : G ≃g turanGraph n r := by
  sorry

end SimpleGraph
