import Mathlib.Data.List.EditDistance.Defs

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
theorem levenshtein_eq_of_zero' {C : Levenshtein.Cost α α δ} [LinearOrderedAddCommMonoid δ]
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

theorem levenshtein_eq_of_zero [DecidableEq α]
    {xs ys : List α} (w : levenshtein Levenshtein.default xs ys = 0) : xs = ys :=
  levenshtein_eq_of_zero' (by simp) (by simp) (by simp) (by simp; tauto) w


def Levenshtein.Cost.flip (C : Cost α β δ) : Cost β α δ where
  insert a := C.delete a
  delete b := C.insert b
  substitute a b := C.substitute b a

theorem levenshtein_symm [AddZeroClass δ] [LinearOrder δ]
    (xs : List α) (ys : List β) :
    levenshtein C xs ys =
      levenshtein C.flip ys xs := by
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




theorem levenshtein_le_insert {C : Levenshtein.Cost α α δ} [LinearOrderedAddCommMonoid δ]
    (hinsert : ∀ a, 0 ≤ C.insert a) (hdelete : ∀ a, 0 ≤ C.delete a)
    (x : α) (xs ys) :
    levenshtein C xs ys ≤ C.insert x + levenshtein C (x :: xs) ys := by
  induction ys generalizing x xs with
  | nil =>
    simp only [levenshtein_cons_nil]
    refine le_add_of_nonneg_of_le (hinsert x) (le_add_of_nonneg_left (hdelete x))
  | cons y ys ihy =>
    simp only [levenshtein_cons_cons]
    rw [←min_add_add_left, ←min_add_add_left]
    simp
    sorry
    -- err, this is much harder than it looks

theorem levenshtein_trans {C : Levenshtein.Cost α α δ} [LinearOrderedAddCommMonoid δ]
    (hinsert : ∀ a, 0 ≤ C.insert a) (hdelete : ∀ a, 0 ≤ C.delete a)
    (hsubstitute₁ : ∀ a b, 0 ≤ C.substitute a b) (hsubstitute₂ : ∀ a, C.substitute a a = 0)
    (hsubstitute₃ : ∀ a b c, C.substitute a c ≤ C.substitute a b + C.substitute b c)
    (xs ys zs : List α) :
    levenshtein C xs zs ≤
      levenshtein C xs ys +
      levenshtein C ys zs := by
  induction xs generalizing ys zs with
  | nil => sorry
  | cons x xs ihx =>
    induction zs generalizing ys with
    | nil => sorry
    | cons z zs ihz =>
      induction ys with
      | nil => sorry
      | cons y ys ihy =>
        simp only [levenshtein_cons_cons x xs y ys]
        rw [←min_add_add_right, ←min_add_add_right]
        simp only [le_min_iff]
        refine ⟨?_, ?_, ?_⟩
        · simp only [levenshtein_cons_cons x xs z zs]
          apply min_le_of_left_le
          rw [add_assoc]
          exact add_le_add_left (ihx (y :: ys) (z :: zs)) (C.delete x)
        · simp only [levenshtein_cons_cons y ys z zs]
          rw [←min_add_add_left, ←min_add_add_left]
          simp only [le_min_iff]
          refine ⟨?_, ?_, ?_⟩
          · sorry -- easy
          · simp only [levenshtein_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_left_le
            rw [add_left_comm]
            apply add_le_add_left
            refine (ihz ys).trans ?_
            rw [add_comm (C.insert y), add_assoc]
            apply add_le_add_left
            apply levenshtein_le_insert hinsert hdelete
          · simp only [levenshtein_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_left_le
            sorry -- easy, although needs another hypothesis!
        · simp only [levenshtein_cons_cons y ys z zs]
          rw [←min_add_add_left, ←min_add_add_left]
          simp only [le_min_iff]
          refine ⟨?_, ?_, ?_⟩
          · sorry -- easy
          · simp only [levenshtein_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_left_le
            rw [add_left_comm]
            apply add_le_add_left
            refine (ihz (y :: ys)).trans ?_
            apply add_le_add_right
            simp only [levenshtein_cons_cons x xs y ys]
            apply min_le_of_right_le
            apply min_le_of_right_le
            rfl
          · simp only [levenshtein_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_right_le
            calc
              _ ≤ _ := add_le_add_right (hsubstitute₃ x y z) _
              _ ≤ _ := add_le_add_left (ihx ys zs) _
              _ = _ := by abel
