/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.Infix
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.EditDistance.Defs

/-!
# Lower bounds for Levenshtein distances

We show that there is some suffix `L'` of `L` such
that the Levenshtein distance from `L'` to `M` gives a lower bound
for the Levenshtein distance from `L` to `m :: M`.

This allows us to use the intermediate steps of a Levenshtein distance calculation
to produce lower bounds on the final result.
-/

variable {C : Levenshtein.Cost α β δ}

theorem levenshtein_bound' [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a, 0 ≤ C.delete a) (hinsert : ∀ b, 0 ≤ C.insert b)
    (hsubstitute : ∀ a b, 0 ≤ C.substitute a b) (xs : List α) (y ys) :
    (suffixLevenshtein C xs ys).1.minimum ≤ levenshtein C xs (y :: ys) := by
  induction xs with
  | nil =>
      simp only [suffixLevenshtein_nil', levenshtein_nil_cons,
        List.minimum_singleton, WithTop.coe_le_coe]
      exact le_add_of_nonneg_left (hinsert y)
  | cons x xs ih =>
    simp only [levenshtein_cons_cons]
    simp only [ge_iff_le, le_min_iff, min_le_iff, WithTop.coe_min, WithTop.coe_le_coe]
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ (suffixLevenshtein C xs ys).1.minimum := by
            simp [suffixLevenshtein_cons₁_fst, List.minimum_cons]
        _ ≤ ↑(levenshtein C xs (y :: ys)) := ih
        _ ≤ _ := by
            simpa using le_add_of_nonneg_left (hdelete x)
    · calc
        (suffixLevenshtein C (x :: xs) ys).1.minimum ≤ ↑(levenshtein C (x :: xs) ys) := by
            simp [suffixLevenshtein_cons₁_fst, List.minimum_cons]
        _ ≤ _ := by
            simpa using le_add_of_nonneg_left (hinsert y)
    · calc
        (suffixLevenshtein C (x :: xs) ys).1.minimum ≤ ↑(levenshtein C xs ys) := by
            simp only [suffixLevenshtein_cons₁_fst, List.minimum_cons]
            apply min_le_of_right_le
            cases xs
            · simp [suffixLevenshtein_nil']
            · simp [suffixLevenshtein_cons₁, List.minimum_cons]
        _ ≤ _ := by
            simpa using le_add_of_nonneg_left (hsubstitute x y)

theorem levenshtein_bound [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a, 0 ≤ C.delete a) (hinsert : ∀ b, 0 ≤ C.insert b)
    (hsubstitute : ∀ a b, 0 ≤ C.substitute a b) (xs : List α) (y ys) :
    ∃ xs', xs' <:+ xs ∧ levenshtein C xs' ys ≤ levenshtein C xs (y :: ys) := by
  simpa [suffixLevenshtein_eq_tails_map, List.minimum_le_coe_iff] using
    levenshtein_bound' hdelete hinsert hsubstitute xs y ys
