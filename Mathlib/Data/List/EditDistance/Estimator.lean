import Mathlib.Data.List.EditDistance.Bounds
import Mathlib.Order.Estimator

theorem List.maximum_ne_bot_of_length_pos [LinearOrder α]
    {L : List α} (h : 0 < L.length) : L.maximum ≠ ⊥ :=
  match L, h with
  | _ :: _, _ => by simp [List.maximum_cons]

theorem List.minimum_ne_top_of_length_pos [LinearOrder α]
    {L : List α} (h : 0 < L.length) : L.minimum ≠ ⊤ :=
  @List.maximum_ne_bot_of_length_pos αᵒᵈ _ _ h

def List.maximum_length_pos [LinearOrder α] {L : List α} (h : 0 < L.length) : α :=
  WithBot.unbot L.maximum (List.maximum_ne_bot_of_length_pos h)

def List.minimum_length_pos [LinearOrder α] {L : List α} (h : 0 < L.length) : α :=
  @List.maximum_length_pos αᵒᵈ _ _ h

theorem WithBot.le_unbot_iff [LE α] {a : α} {b : WithBot α} (h : b ≠ ⊥) :
    a ≤ WithBot.unbot b h ↔ (a : WithBot α) ≤ b := by
  match b, h with
  | some _, _ => simp

theorem WithTop.untop_le_iff [LE α] {a : WithTop α} {b : α} (h : a ≠ ⊤) :
    WithTop.untop a h ≤ b ↔ a ≤ (b : WithBot α) :=
  @WithBot.le_unbot_iff αᵒᵈ _ _ _ _

theorem List.le_maximum_length_pos_iff [LinearOrder α] {L : List α} (h : 0 < L.length) :
    b ≤ List.maximum_length_pos h ↔ b ≤ L.maximum :=
  WithBot.le_unbot_iff _

theorem List.minimum_length_pos_le_iff [LinearOrder α] {L : List α} (h : 0 < L.length) :
    List.minimum_length_pos h ≤ b ↔ L.minimum ≤ b :=
  @List.le_maximum_length_pos_iff αᵒᵈ _ _ _ h

structure LevenshteinEstimator [CanonicallyLinearOrderedAddMonoid δ]
    (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β) where
  pre_rev : List β
  suff : List β
  split : pre_rev.reverse ++ suff = ys
  distances : Σ' (r : List δ), 0 < r.length
  distances_eq : distances = suffixLevenshtein C xs suff
  bound : δ
  bound_eq : bound = match pre_rev with
    | [] => distances.1[0]'(distances.2)
    | _ => List.minimum_length_pos distances.2

instance [CanonicallyLinearOrderedAddMonoid δ] (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β) :
    EstimatorData (levenshtein C xs ys) (LevenshteinEstimator C xs ys) where
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

instance [CanonicallyLinearOrderedAddMonoid δ] (C : Levenshtein.Cost α β δ) (xs : List α) (ys : List β) :
    Estimator (levenshtein C xs ys) (LevenshteinEstimator C xs ys) where
  bound_le e := match e.pre_rev, e.split, e.bound_eq with
  | [], split, eq => by
    simp only [List.reverse_nil, List.nil_append] at split
    rw [e.distances_eq] at eq
    simp only [List.getElem_eq_get] at eq
    rw [split] at eq
    exact eq.le
  | y :: t, split, eq => by
    rw [e.distances_eq] at eq
    simp at eq
    dsimp [EstimatorData.bound]
    rw [eq]
    simp only [←split]
    simp only [List.minimum_length_pos_le_iff]
    exact (suffixLevenshtein_minimum_le_levenshtein_append _ _ _)
  improve_spec e := by
    dsimp [EstimatorData.improve]
    match e.pre_rev, e.split, e.bound_eq with
    | [], split, eq =>
      simp only [List.reverse_nil, List.nil_append] at split
      rw [e.distances_eq] at eq
      simp only [List.getElem_eq_get] at eq
      rw [split] at eq
      exact eq
    | y :: t, split, eq =>
      dsimp
