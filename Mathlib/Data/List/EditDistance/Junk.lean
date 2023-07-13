
-- @[simp] theorem Array.size_append (x y : Array α) : (x ++ y).size = x.size + y.size := sorry
-- @[simp] theorem Subarray.size_toSubarray_fin (x : Array α) (i : Fin (x.size + 1)) : x[:i].size = i := sorry
-- @[simp] theorem Array.size_ofSubarray (x : Subarray α) : Array.size (.ofSubarray x) = x.size := sorry

-- structure Edit [Add α] (a b : α) where
--   left : α
--   right : α
--   before : α
--   after : α
--   eq_before : a = left + before + right
--   eq_after : b = left + after + right

-- def editQuiver (α : Type _) := α

-- def editQuiver_equiv : α ≃ editQuiver α := Equiv.refl _

-- instance [Add α] : Quiver (editQuiver α) where
--   Hom (a b : α) := Edit a b

-- open CategoryTheory

-- def editCategory (α : Type _) [Add α] := Paths (editQuiver α)
-- instance [Add α] : Category (editCategory α) := inferInstanceAs <| Category (Paths _)

-- def editCategory_equiv [Add α] : α ≃ editCategory α := Equiv.refl _

-- def editCost [Add α] [AddZeroClass β] (cost : α → α → β) {x y : editCategory α} : (x ⟶ y) → β
--   | .nil => 0
--   | .cons p e => editCost cost p + cost e.before e.after

-- /-- Edit distance is the length of the shortest path in the edit graph. -/
-- def geodesicEditDistance [Add α] [AddZeroClass β] [InfSet β] (cost : α → α → β) (x y : α) : β :=
--   ⨅ (p : editCategory_equiv x ⟶ editCategory_equiv y), editCost cost p

-- def AddAntidiagonal {α : Type _} [Add α] (x : α) : Type _ := { p : α × α // p.1 + p.2 = x }

-- instance [Add α] [DecidableEq α] (x : α) : DecidableEq (AddAntidiagonal x) :=
--   inferInstanceAs <| DecidableEq (Subtype _)

-- def addAntidiagonal [Add α] (x : α) : Set (α × α) :=
--   Set.range (Subtype.val : AddAntidiagonal x → _)

-- def addAntidiagonalList [Add α] (x : α) [FinEnum (AddAntidiagonal x)] : List (α × α) :=
--   FinEnum.toList (AddAntidiagonal x) |>.map (·.1)

-- theorem FinEnum.mem_toList_map_val (p : α → Prop) [FinEnum {x // p x}] :
--     x ∈ (FinEnum.toList {x // p x} |>.map Subtype.val) ↔ p x :=
--   by simp

-- @[simp] theorem addAntidiagonalList_mem [Add α] (x : α) [I : FinEnum (AddAntidiagonal x)] :
--     p ∈ addAntidiagonalList x ↔ p.1 + p.2 = x :=
--   @FinEnum.mem_toList_map_val _ _ (fun p : α × α => p.1 + p.2 = x) I

-- instance : Add (Array α) where
--   add := Array.append

-- instance [DecidableEq α] (x : Array α) : FinEnum (AddAntidiagonal x) where
--   card := x.size + 1
--   equiv :=
--   { toFun := fun p => ⟨p.1.1.size, sorry⟩
--     invFun := fun i => ⟨(x[:i].toArray, x[i:].toArray), sorry⟩
--     left_inv := sorry,
--     right_inv := sorry, }

-- instance : Add (List α) where
--   add := List.append

-- instance [DecidableEq α] (x : List α) : FinEnum (AddAntidiagonal x) where
--   card := x.length + 1
--   equiv :=
--   { toFun := fun p => ⟨p.1.1.length, sorry⟩
--     invFun := fun i => ⟨(x.take i, x.drop i), sorry⟩
--     left_inv := sorry,
--     right_inv := sorry, }

-- open BigOperators

-- def partitionEditDistance [InfSet β] [AddCommMonoid β] (cost : α → α → β)
--     [AddZeroClass α] (x y : α) : β :=
--   ⨅ (n : ℕ) (xs : Vector α n) (ys : Vector α n) (xh : xs.toList.sum = x) (yh : ys.toList.sum = y),
--     ∑ i : Fin n, cost xs[i] ys[i]

-- variable (cost : List α → List α → β) [InfSet β] [Add β]

-- /-- A noncomputable definition of edit distance. -/
-- def editDistance' (x y : List α) : β :=
--   ⨅ (p : addAntidiagonal x) (q : addAntidiagonal y),
--     if p.1.1.length + q.1.1.length < x.length + y.length then
--       editDistance' p.1.1 q.1.1 + cost p.1.2 q.1.2
--     else
--       cost x y
-- termination_by editDistance' x y => x.length + y.length

-- variable [DecidableEq α] [Min β] [Top β]

-- /-- A computable, but completely unoptimized, definition of the (generalized) edit distance. -/
-- def editDistance (x y : List α) : β := Id.run do
--   let mut b := cost x y
--   for (x₁, x₂) in addAntidiagonalList x do
--     for (y₁, y₂) in addAntidiagonalList y do
--       if x₁.length + y₁.length < x.length + y.length then
--         b := min b (editDistance x₁ y₁ + cost x₂ y₂)
--   return b
-- termination_by editDistance x y => x.length + y.length

-- section levenshtein

-- variable [Zero β] [Top β]

-- def generalizedLevenshteinCost (delete insert : α → β) (substitute : α → α → β) (x y : List α) :=
--   match x, y with
--   | [], [] => (0 : β)
--   | [], [a] => insert a
--   | [a], [] => delete a
--   | [a], [b] => substitute a b
--   | _, _ => ⊤

-- variable [One β] [DecidableEq α]

-- def levenshteinCost : List α → List α → β :=
--   generalizedLevenshteinCost (fun _ => (1 : β)) (fun _ => (1 : β))
--     (fun a b => if a = b then 0 else 1)

-- #eval (editDistance levenshteinCost "kitten".toList "sitting".toList : WithTop ℕ)


-- Err... what hypotheses does this need?
-- @[simp]
-- theorem levenshtein_cons_self [LinearOrderedAddCommMonoid δ]
--     {delete : α → δ} {insert : α → δ} {substitute : α → α → δ}
--     (hdelete : ∀ a, 0 ≤ delete a) (hinsert : ∀ a, 0 ≤ insert a)
--     (hsubstitute : ∀ a, substitute a a = 0) (a xs ys) :
--     levenshtein delete insert substitute (a :: xs) (a :: ys) =
--       levenshtein delete insert substitute xs ys := by
--   sorry


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
