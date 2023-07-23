/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.EditDistance.Bounds
import Mathlib.Order.Estimator
import Mathlib.Util.Time

theorem WithBot.le_unbot_iff [LE α] {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a ≤ WithBot.unbot b h ↔ (a : WithBot α) ≤ b := by
  match b, h with
  | some _, _ => simp only [unbot_coe, coe_le_coe]

theorem WithTop.untop_le_iff [LE α] {a : WithTop α} {b : α} (h : a ≠ ⊤) :
    WithTop.untop a h ≤ b ↔ a ≤ (b : WithBot α) :=
  @WithBot.le_unbot_iff αᵒᵈ _ _ _ _

#find_home WithBot.le_unbot_iff

section
variable [LinearOrder α]

theorem List.maximum_ne_bot_of_length_pos {L : List α} (h : 0 < L.length) : L.maximum ≠ ⊥ :=
  match L, h with
  | _ :: _, _ => by simp [List.maximum_cons]

theorem List.minimum_ne_top_of_length_pos {L : List α} (h : 0 < L.length) : L.minimum ≠ ⊤ :=
  @List.maximum_ne_bot_of_length_pos αᵒᵈ _ _ h

#find_home List.maximum_ne_bot_of_length_pos

def List.maximum_of_length_pos {L : List α} (h : 0 < L.length) : α :=
  WithBot.unbot L.maximum (List.maximum_ne_bot_of_length_pos h)

def List.minimum_of_length_pos {L : List α} (h : 0 < L.length) : α :=
  @List.maximum_of_length_pos αᵒᵈ _ _ h

@[simp]
lemma List.coe_maximum_of_length_pos {L : List α} (h : 0 < L.length) :
    (L.maximum_of_length_pos h : α) = L.maximum :=
  WithBot.coe_unbot _ _

@[simp]
lemma List.coe_minimum_of_length_pos {L : List α} (h : 0 < L.length) :
    (L.minimum_of_length_pos h : α) = L.minimum :=
  WithTop.coe_untop _ _

theorem List.le_maximum_of_length_pos_iff {L : List α} (h : 0 < L.length) :
    b ≤ List.maximum_of_length_pos h ↔ b ≤ L.maximum :=
  WithBot.le_unbot_iff _

theorem List.minimum_of_length_pos_le_iff {L : List α} (h : 0 < L.length) :
    List.minimum_of_length_pos h ≤ b ↔ L.minimum ≤ b :=
  @List.le_maximum_of_length_pos_iff αᵒᵈ _ _ _ h

theorem List.le_maximum_of_length_pos_of_mem {L : List α} (h : a ∈ L) (w : 0 < L.length) :
     a ≤ L.maximum_of_length_pos w := by
  simp [List.le_maximum_of_length_pos_iff]
  exact List.le_maximum_of_mem' h

theorem List.minimum_of_length_pos_le_of_mem {L : List α} (h : a ∈ L) (w : 0 < L.length) :
     L.minimum_of_length_pos w ≤ a :=
  @List.le_maximum_of_length_pos_of_mem αᵒᵈ _ _ _ h _

theorem List.getElem_le_maximum_of_length_pos {L : List α} (w : i < L.length) :
    L[i] ≤ L.maximum_of_length_pos (Nat.zero_lt_of_lt w) := by
  apply List.le_maximum_of_length_pos_of_mem
  exact get_mem L i w

theorem List.minimum_of_length_pos_le_getElem {L : List α} (w : i < L.length) :
    L.minimum_of_length_pos (Nat.zero_lt_of_lt w) ≤ L[i] :=
  @List.getElem_le_maximum_of_length_pos αᵒᵈ _ _ _ _

end

variable [CanonicallyLinearOrderedAddMonoid δ]
    (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β)

structure LevenshteinEstimator' : Type _ where
  pre_rev : List β
  suff : List β
  split : pre_rev.reverse ++ suff = ys
  distances : Σ' (r : List δ), 0 < r.length
  distances_eq : distances = suffixLevenshtein C xs suff
  bound : δ × ℕ
  bound_eq : bound = match pre_rev with
    | [] => (distances.1[0]'(distances.2), ys.length)
    | _ => (List.minimum_of_length_pos distances.2, suff.length)

instance : EstimatorData (Thunk.mk fun _ => (levenshtein C xs ys, ys.length)) (LevenshteinEstimator' C xs ys) where
  bound e := e.bound
  improve e := match e.pre_rev, e.split with
    | [], _ => none
    | y :: ys, split => some
      { pre_rev := ys
        suff := y :: e.suff
        split := by simpa using split
        distances := Levenshtein.impl C xs y e.distances
        distances_eq := suffixLevenshtein_eq xs y e.suff e.distances_eq
        bound := _
        bound_eq := rfl }

instance estimator' : Estimator (Thunk.mk fun _ => (levenshtein C xs ys, ys.length)) (LevenshteinEstimator' C xs ys) where
  bound_le e := match e.pre_rev, e.split, e.bound_eq with
  | [], split, eq => by
    simp only [List.reverse_nil, List.nil_append] at split
    rw [e.distances_eq] at eq
    simp only [List.getElem_eq_get] at eq
    rw [split] at eq
    exact eq.le
  | y :: t, split, eq => by
    rw [e.distances_eq] at eq
    simp only at eq
    dsimp [EstimatorData.bound]
    rw [eq]
    simp only [←split]
    constructor
    · simp only [List.minimum_of_length_pos_le_iff]
      exact suffixLevenshtein_minimum_le_levenshtein_append _ _ _
    · exact List.length_le_of_sublist (List.sublist_append_right _ _)
  improve_spec e := by
    dsimp [EstimatorData.improve]
    match e.pre_rev, e.split, e.bound_eq, e.distances_eq with
    | [], split, eq, _ =>
      simp only [List.reverse_nil, List.nil_append] at split
      rw [e.distances_eq] at eq
      simp only [List.getElem_eq_get] at eq
      rw [split] at eq
      exact eq
    | [y], split, b_eq, d_eq =>
      simp only [EstimatorData.bound, Prod.lt_iff, List.reverse_nil, List.nil_append]
      right
      simp at b_eq
      rw [b_eq]
      constructor
      · refine (?_ : _ ≤ _).trans (List.minimum_of_length_pos_le_getElem _)
        simp only [List.minimum_of_length_pos_le_iff, List.coe_minimum_of_length_pos, d_eq]
        apply le_suffixLevenshtein_cons_minimum
      · simp [←split]
    | y₁ :: y₂ :: t, split, b_eq, d_eq =>
      simp only [EstimatorData.bound, Prod.lt_iff]
      right
      simp at b_eq
      rw [b_eq]
      constructor
      · simp only [d_eq, List.minimum_of_length_pos_le_iff, List.coe_minimum_of_length_pos]
        apply le_suffixLevenshtein_cons_minimum
      · exact Nat.lt.base _

/-- An estimator for Levenshtein distances. -/
def LevenshteinEstimator : Type _ :=
  Estimator.fst (Thunk.mk fun _ => (levenshtein C xs ys, ys.length)) (LevenshteinEstimator' C xs ys)

instance [∀ a : δ × ℕ, WellFoundedGT { x // x ≤ a }] :
    Estimator (Thunk.mk fun _ => levenshtein C xs ys) (LevenshteinEstimator C xs ys) :=
  @instEstimatorFst _ _ _ _ _ _ (Thunk.mk fun _ => _) (Thunk.mk fun _ => _) _ (estimator' C xs ys)

/-- The trivial estimator for Levenshtein distances. -/
instance [CanonicallyLinearOrderedAddMonoid δ]
    (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β) :
    Bot (LevenshteinEstimator C xs ys) where
  bot :=
  { inner :=
    { pre_rev := ys.reverse
      suff := []
      split := by simp
      distances_eq := rfl
      bound_eq := rfl } }
