/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.EditDistance.Defs

/-!
# Levenshtein distances give a metric

We show that with suitable hypotheses on the cost function,
Levenshtein distance is non-negative, and zero iff the lists are identical.

We show that it is symmetric.

For now we do not prove the triangle inequality.

(This is a bit harder, as I don't think it can be proved just by
some inductive argument from the definition.
Instead we need to look at the geodesic distance on the edit graph,
and argue that every minimal path can be put in the form:
"repeatedly: edit an initial character, then edit the suffix".)
-/

variable {C : Levenshtein.Cost α β δ}

theorem levenshtein_nonneg [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a, 0 ≤ C.delete a) (hinsert : ∀ b, 0 ≤ C.insert b)
    (hsubstitute₁ : ∀ a b, 0 ≤ C.substitute a b) (xs : List α) (ys : List β) :
    0 ≤ levenshtein C xs ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp
    | cons y ys ihy =>
      simp only [levenshtein_nil_cons]
      exact add_nonneg (hinsert y) ihy
  | cons x xs ihx =>
    induction ys with
    | nil =>
      simp only [levenshtein_cons_nil]
      exact add_nonneg (hdelete x) (ihx [])
    | cons y ys ihy =>
      simp only [levenshtein_cons_cons, ge_iff_le, le_min_iff, min_le_iff]
      refine ⟨?_, ?_, ?_⟩ <;>
        apply add_nonneg <;>
          solve_by_elim

theorem levenshtein_refl {C : Levenshtein.Cost α α δ} [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a, 0 ≤ C.delete a) (hinsert : ∀ a, 0 ≤ C.insert a)
    (hsubstitute₁ : ∀ a b, 0 ≤ C.substitute a b)
    (hsubstitute₂ : ∀ a, C.substitute a a = 0)
    (xs : List α) : levenshtein C xs xs = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [levenshtein_cons_cons, hsubstitute₂, ih]
    simp only [add_zero]
    -- TODO we would prefer to rewrite at the second `min`,
    -- but this is slightly awkward to do as side conditions from rewrites
    -- block closing `conv` blocks.
    rw [min_eq_right]
    · rw [min_eq_right]
      exact add_nonneg (hinsert _)
        (levenshtein_nonneg hdelete hinsert hsubstitute₁ (x :: xs) xs)
    · rw [min_eq_right]
      · exact add_nonneg (hdelete _)
          (levenshtein_nonneg hdelete hinsert hsubstitute₁ xs (x :: xs))
      · exact add_nonneg (hinsert _)
          (levenshtein_nonneg hdelete hinsert hsubstitute₁ (x :: xs) xs)

-- These two theorems are perhaps not generally useful,
-- so we leave them here for now.
theorem left_eq_of_min_eq_lt [LinearOrder α] {a b c : α} (w : min a b = c) (h : c < b) : a = c := by
  rw [min_eq_iff] at w
  rcases w with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rfl
  · exfalso; apply lt_irrefl b; exact h

theorem right_eq_of_min_eq_lt [LinearOrder α] {a b c : α} (w : min a b = c) (h : c < a) : b = c := by
  rw [min_eq_iff] at w
  rcases w with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exfalso; apply lt_irrefl a; exact h
  · rfl

/--
Given suitable hypotheses on the cost functions,
the Levenshtein distance is zero only if the lists are the same.
-/
theorem levenshtein_eq_of_zero {C : Levenshtein.Cost α α δ} [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a, 0 < C.delete a) (hinsert : ∀ a, 0 < C.insert a)
    (hsubstitute₁ : ∀ a b, 0 ≤ C.substitute a b)
    (hsubstitute₂ : ∀ a b, C.substitute a b = 0 ↔ a = b)
    {xs ys : List α}
    (w : levenshtein C xs ys = 0) : xs = ys := by
  have nonneg := (levenshtein_nonneg
    (fun a => (hdelete a).le) (fun a => (hinsert a).le) hsubstitute₁)
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      exfalso
      simp only [levenshtein_nil_cons] at w
      apply lt_irrefl (0 : δ)
      conv => congr; rfl; rw [←w]
      exact add_pos_of_pos_of_nonneg (hinsert _) (nonneg _ _)
  | cons x xs ihx =>
    cases ys with
    | nil =>
      exfalso
      simp only [levenshtein_cons_nil] at w
      apply lt_irrefl (0 : δ)
      conv => congr; rfl; rw [←w]
      exact add_pos_of_pos_of_nonneg (hdelete _) (nonneg _ _)
    | cons y ys =>
      simp only [levenshtein_cons_cons] at w
      replace w := right_eq_of_min_eq_lt w ?_
      replace w := right_eq_of_min_eq_lt w ?_
      · replace w : C.substitute x y = 0 ∧ levenshtein C xs ys = 0 :=
          (add_eq_zero_iff' (hsubstitute₁ x y) (nonneg _ _)).mp w
        rw [hsubstitute₂] at w
        obtain ⟨rfl, w⟩ := w
        congr
        apply ihx w
      · exact add_pos_of_pos_of_nonneg (hinsert _) (nonneg _ _)
      · exact add_pos_of_pos_of_nonneg (hdelete _) (nonneg _ _)

/-- Reverse the source and target in a Levenshtein cost structure. -/
def Levenshtein.Cost.flip (C : Cost α β δ) : Cost β α δ where
  insert a := C.delete a
  delete b := C.insert b
  substitute a b := C.substitute b a

theorem levenshtein_symm [AddZeroClass δ] [LinearOrder δ] (xs : List α) (ys : List β) :
    levenshtein C xs ys = levenshtein C.flip ys xs := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp
    | cons y ys ih => simp [ih]; rfl
  | cons x xs ih₁ =>
    induction ys with
    | nil => simp [ih₁]; rfl
    | cons y ys ih₂ =>
      simp only [List.map_cons, levenshtein_cons_cons, ih₁, ih₂]
      rw [← min_assoc, min_comm (C.delete x + _), min_assoc]
      rfl
