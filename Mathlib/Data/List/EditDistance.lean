import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.MinMax
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Combinatorics.Quiver.Path
-- import Mathlib.CategoryTheory.PathCategory
-- import Mathlib.Data.FinEnum


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

-- section levenshteinDistance

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

section AddZeroClass
variable [AddZeroClass δ]

section Min
variable [Min δ]

/--
(Implementation detail for `levenshteinDistance`)

Given a list `xs` and the Levenshtein distances from each suffix of `xs` to some other list `ys`,
compute the Levenshtein distances from each suffix of `xs` to `y :: ys`.

(Note that we don't actually need to know `ys` itself here, so it is not an argument.)

The return value is a list of length `x.length + 1`,
and it is convenient for the recursive calls that we bundle this list
with a proof that it is non-empty.
-/
def levenshteinSuffixDistances_impl (delete : α → δ) (insert : β → δ) (substitute : α → β → δ)
    (xs : List α) (y : β) (d : Σ' (r : List δ), 0 < r.length) : Σ' (r : List δ), 0 < r.length :=
  let ⟨ds, w⟩ := d
  xs.zip (ds.zip ds.tail) |>.foldr
    (init := ⟨[insert y + ds.getLast (List.length_pos.mp w)], by simp⟩)
    (fun ⟨x, d₀, d₁⟩ ⟨r, w⟩ =>
      ⟨min (delete x + r[0]) (min (insert y + d₀) (substitute x y + d₁)) :: r, by simp⟩)

-- Note this lemma has an unspecified proof `w'` on the right-hand-side,
-- which will become an extra goal when rewriting.
theorem levenshteinSuffixDistances_impl_cons {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (x) (xs) (y) (d) (ds) (w) (w') :
    levenshteinSuffixDistances_impl delete insert substitute (x :: xs) y ⟨d :: ds, w⟩ =
      let ⟨r, w⟩ := levenshteinSuffixDistances_impl delete insert substitute xs y ⟨ds, w'⟩
      ⟨min
        (delete x + r[0])
        (min
          (insert y + d)
          (substitute x y + ds[0])) :: r, by simp⟩ :=
  match ds, w' with | _ :: _, _ => rfl

theorem levenshteinSuffixDistances_impl_cons_fst_zero
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (x) (xs) (y) (d) (ds) (w) (h) (w') :
    (levenshteinSuffixDistances_impl delete insert substitute (x :: xs) y ⟨d :: ds, w⟩).1[0] =
      let ⟨r, w⟩ := levenshteinSuffixDistances_impl delete insert substitute xs y ⟨ds, w'⟩
      min
        (delete x + r[0])
        (min
          (insert y + d)
          (substitute x y + ds[0])) :=
  match ds, w' with | _ :: _, _ => rfl

theorem levenshteinSuffixDistances_impl_length {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (xs) (y) (d) (w : d.1.length = xs.length + 1) :
    (levenshteinSuffixDistances_impl delete insert substitute xs y d).1.length =
      xs.length + 1 := by
  induction xs generalizing d
  · case nil =>
    rfl
  · case cons x xs ih =>
    dsimp [levenshteinSuffixDistances_impl]
    match d, w with
    | ⟨d₁ :: d₂ :: ds, _⟩, w =>
      dsimp
      congr 1
      refine ih ⟨d₂ :: ds, (by simp)⟩ (by simpa using w)

/--
`levenshteinSuffixDistances delete insert substitute x y` computes the Levenshtein distance
(using the cost functions `delete insert : α → δ` and `substitute : α → α → δ`)
from each suffix of the list `x` to the list `y`.

The first element of this list is the Levenshtein distance from `x` to `y`.

Note that if the cost functions do not satisfy the inequalities
* `delete a + insert b ≥ substitute a b`
* `substitute a b + substitute b c ≥ substitute a c`
(or if any values are negative)
then the edit distances calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshteinSuffixDistances (delete : α → δ) (insert : β → δ) (substitute : α → β → δ) (xs : List α) (ys : List β) :
    Σ' (r : List δ), 0 < r.length :=
  ys.foldr
    (levenshteinSuffixDistances_impl delete insert substitute xs)
    (xs.foldr (init := ⟨[0], by simp⟩) (fun a ⟨r, w⟩ => ⟨(delete a + r[0]) :: r, by simp⟩))

theorem levenshteinSuffixDistances_length {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (xs : List α) (ys : List β) :
    (levenshteinSuffixDistances delete insert substitute xs ys).1.length = xs.length + 1 := by
  induction ys
  · case nil =>
    dsimp [levenshteinSuffixDistances]
    induction xs
    · case nil => rfl
    · case cons _ xs ih =>
      simp_all
  · case cons y ys ih =>
    dsimp [levenshteinSuffixDistances]
    rw [levenshteinSuffixDistances_impl_length]
    exact ih




/--
`levenshteinDistance delete insert substitute x y` computes the Levenshtein distance
(using the cost functions `delete insert : α → β` and `substitute : α → α → β`)
from the list `x` to the list `y`.

Note that if the cost functions do not satisfy the inequalities
* `delete a + insert b ≥ substitute a b`
* `substitute a b + substitute b c ≥ substitute a c`
(or if any values are negative)
then the edit distance calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshteinDistance (delete : α → δ) (insert : β → δ) (substitute : α → β → δ) (xs : List α) (ys : List β) : δ :=
  let ⟨r, w⟩ := levenshteinSuffixDistances delete insert substitute xs ys
  r[0]

theorem levenshteinSuffixDistances_nil_nil {delete : α → δ} {insert : β → δ} {substitute : α → β → δ} :
    (levenshteinSuffixDistances delete insert substitute [] []).1 = [0] := by
  rfl

-- theorem levenshteinSuffixDistances_nil_cons (delete insert : α → β) (substitute : α → α → β)
--     (y) (ys):
--     (levenshteinSuffixDistances delete insert substitute [] (y :: ys)).1 =
--        (levenshteinSuffixDistances delete insert substitute [] ys).1.map
--          fun d => insert y + d := by
--   sorry

-- FIXME, find home
theorem List.eq_of_length_one (x : List α) (w : x.length = 1) :
    have : 0 < x.length := (lt_of_lt_of_eq zero_lt_one w.symm)
    x = [x[0]] := by
  match x, w with
  | [r], _ => rfl

theorem levenshteinSuffixDistances_nil'
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ} (ys) :
    (levenshteinSuffixDistances delete insert substitute [] ys).1 =
      [levenshteinDistance delete insert substitute [] ys] :=
  List.eq_of_length_one _ (levenshteinSuffixDistances_length [] _)

theorem levenshteinSuffixDistances_cons₂
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (xs y ys) :
    levenshteinSuffixDistances delete insert substitute xs (y :: ys) =
      (levenshteinSuffixDistances_impl delete insert substitute xs) y
        (levenshteinSuffixDistances delete insert substitute xs ys) :=
  rfl

theorem ext_helper {x y : Σ' (r : List β), 0 < r.length}
    (w₀ : x.1[0]'x.2 = y.1[0]'y.2) (w : x.1.tail = y.1.tail) : x = y := by
  match x, y with
  | ⟨hx :: tx, _⟩, ⟨hy :: ty, _⟩ => simp_all

theorem levenshteinSuffixDistances_cons₁
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ} (x) (xs ys) :
    levenshteinSuffixDistances delete insert substitute (x :: xs) ys =
      ⟨levenshteinDistance delete insert substitute (x :: xs) ys ::
        (levenshteinSuffixDistances delete insert substitute xs ys).1, by simp⟩ := by
  induction ys
  · case nil =>
    dsimp [levenshteinDistance, levenshteinSuffixDistances]
  · case cons y ys ih =>
    apply ext_helper
    · rfl
    · rw [levenshteinSuffixDistances_cons₂ (x :: xs), ih, levenshteinSuffixDistances_impl_cons]
      · rfl
      · simp [levenshteinSuffixDistances_length]

theorem levenshteinSuffixDistances_cons_cons_fst_get_zero
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (x xs y ys) (w) :
    (levenshteinSuffixDistances delete insert substitute (x :: xs) (y :: ys)).1[0] =
      let ⟨dx, _⟩ := levenshteinSuffixDistances delete insert substitute xs (y :: ys)
      let ⟨dy, _⟩ := levenshteinSuffixDistances delete insert substitute (x :: xs) ys
      let ⟨dxy, _⟩ := levenshteinSuffixDistances delete insert substitute xs ys
      min
        (delete x + dx[0])
        (min
          (insert y + dy[0])
          (substitute x y + dxy[0])) := by
  conv =>
    lhs
    dsimp only [levenshteinSuffixDistances_cons₂]
  simp only [levenshteinSuffixDistances_cons₁]
  rw [levenshteinSuffixDistances_impl_cons_fst_zero]
  rfl

theorem levenshteinSuffixDistances_eq
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ} (xs ys) :
    (levenshteinSuffixDistances delete insert substitute xs ys).1 =
      xs.tails.map fun xs' => levenshteinDistance delete insert substitute xs' ys := by
  induction xs
  · case nil =>
    simp only [List.map, levenshteinSuffixDistances_nil']
  · case cons x xs ih =>
    simp only [List.map, levenshteinSuffixDistances_cons₁, ih]

@[simp]
theorem levenshteinDistance_nil_nil {delete : α → δ} {insert : β → δ} {substitute : α → β → δ} :
    levenshteinDistance delete insert substitute [] [] = 0 := by
  simp [levenshteinDistance]

@[simp]
theorem levenshteinDistance_nil_cons {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (y : β) (ys : List β) :
    levenshteinDistance delete insert substitute [] (y :: ys) =
      insert y + levenshteinDistance delete insert substitute [] ys := by
  dsimp [levenshteinDistance]
  congr
  rw [List.getLast_eq_get]
  congr
  rw [show (List.length _) = 1 from _]
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr]
    rw [levenshteinSuffixDistances_impl_length] <;> simp [ih]

@[simp]
theorem levenshteinDistance_cons_nil {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (x : α) (xs : List α) :
    levenshteinDistance delete insert substitute (x :: xs) [] =
      delete x + levenshteinDistance delete insert substitute xs [] :=
  rfl

@[simp]
theorem levenshteinDistance_cons_cons {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (x : α) (xs : List α) (y : β) (ys : List β) :
    levenshteinDistance delete insert substitute (x :: xs) (y :: ys) =
      min (delete x + levenshteinDistance delete insert substitute xs (y :: ys))
        (min (insert y + levenshteinDistance delete insert substitute (x :: xs) ys)
          (substitute x y + levenshteinDistance delete insert substitute xs ys)) :=
  levenshteinSuffixDistances_cons_cons_fst_get_zero _ _ _ _ _

end Min

end AddZeroClass

theorem levenshteinDistance_nonneg [LinearOrderedAddCommMonoid δ]
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ}
    (hdelete : ∀ a, 0 ≤ delete a) (hinsert : ∀ b, 0 ≤ insert b)
    (hsubstitute₁ : ∀ a b, 0 ≤ substitute a b) (xs : List α) (ys : List β) :
    0 ≤ levenshteinDistance delete insert substitute xs ys := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp
    | cons y ys ihy =>
      simp only [levenshteinDistance_nil_cons]
      exact add_nonneg (hinsert y) ihy
  | cons x xs ihx =>
    induction ys with
    | nil =>
      simp only [levenshteinDistance_cons_nil]
      exact add_nonneg (hdelete x) (ihx [])
    | cons y ys ihy =>
      simp only [levenshteinDistance_cons_cons, ge_iff_le, le_min_iff, min_le_iff]
      refine ⟨?_, ?_, ?_⟩ <;>
        apply add_nonneg <;>
          solve_by_elim

theorem levenshteinDistance_refl [LinearOrderedAddCommMonoid δ]
    {delete insert : α → δ} {substitute : α → α → δ}
    (hinsert : ∀ a, 0 ≤ insert a) (hdelete : ∀ a, 0 ≤ delete a)
    (hsubstitute₁ : ∀ a b, 0 ≤ substitute a b) (hsubstitute₂ : ∀ a, substitute a a = 0)
    (xs : List α) : levenshteinDistance delete insert substitute xs xs = 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [levenshteinDistance_cons_cons, hsubstitute₂, ih]
    simp only [add_zero]
    -- TODO we would prefer to rewrite at the second `min`,
    -- but this is slightly awkward to do as side conditions from rewrites
    -- block closing `conv` blocks.
    rw [min_eq_right]
    · rw [min_eq_right]
      exact add_nonneg (hinsert _)
        (levenshteinDistance_nonneg hdelete hinsert hsubstitute₁ (x :: xs) xs)
    · rw [min_eq_right]
      · exact add_nonneg (hdelete _)
          (levenshteinDistance_nonneg hdelete hinsert hsubstitute₁ xs (x :: xs))
      · exact add_nonneg (hinsert _)
          (levenshteinDistance_nonneg hdelete hinsert hsubstitute₁ (x :: xs) xs)

theorem levenshteinDistance_eq_of_zero [LinearOrderedAddCommMonoid δ]
    {delete insert : α → δ} {substitute : α → α → δ}
    (hinsert : ∀ a, 0 < insert a) (hdelete : ∀ a, 0 < delete a)
    (hsubstitute₁ : ∀ a b, 0 ≤ substitute a b) (hsubstitute₂ : ∀ a b, substitute a b = 0 ↔ a = b)
    {xs ys : List α}
    (w : levenshteinDistance delete insert substitute xs ys = 0) : xs = ys := by
  -- TODO should be straighforward
  sorry

theorem levenshteinDistance_symm [AddZeroClass δ] [LinearOrder δ]
    {delete : α → δ} {insert : β → δ} {substitute : α → β → δ} (xs : List α) (ys : List β) :
    levenshteinDistance delete insert substitute xs ys =
      levenshteinDistance insert delete (Function.swap substitute) ys xs := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp
    | cons y ys ih => simp [ih]
  | cons x xs ih₁ =>
    induction ys with
    | nil => simp [ih₁]
    | cons y ys ih₂ =>
      simp only [levenshteinDistance_cons_cons, ih₁, ih₂]
      rw [← min_assoc, min_comm (delete x + _), min_assoc]

theorem levenshteinDistance_le_insert [LinearOrderedAddCommMonoid δ] (x xs ys)
    {delete insert : α → δ} {substitute : α → α → δ}
    (hinsert : ∀ a, 0 ≤ insert a) (hdelete : ∀ a, 0 ≤ delete a) :
    levenshteinDistance delete insert substitute xs ys ≤
      insert x + levenshteinDistance delete insert substitute (x :: xs) ys := by

  induction ys generalizing x xs with
  | nil =>
    simp only [levenshteinDistance_cons_nil]
    refine le_add_of_nonneg_of_le (hinsert x) (le_add_of_nonneg_left (hdelete x))
  | cons y ys ihy =>
    simp only [levenshteinDistance_cons_cons]
    rw [←min_add_add_left, ←min_add_add_left]
    simp
    sorry
    -- err, this is much harder than it looks




theorem levenshteinDistance_trans [LinearOrderedAddCommMonoid δ]
    {delete insert : α → δ} {substitute : α → α → δ}
    (hinsert : ∀ a, 0 ≤ insert a) (hdelete : ∀ a, 0 ≤ delete a)
    (hsubstitute₁ : ∀ a b, 0 ≤ substitute a b) (hsubstitute₂ : ∀ a, substitute a a = 0)
    (hsubstitute₃ : ∀ a b c, substitute a c ≤ substitute a b + substitute b c)
    (xs ys zs : List α) :
    levenshteinDistance delete insert substitute xs zs ≤
      levenshteinDistance delete insert substitute xs ys +
      levenshteinDistance delete insert substitute ys zs := by
  induction xs generalizing ys zs with
  | nil => sorry
  | cons x xs ihx =>
    induction zs generalizing ys with
    | nil => sorry
    | cons z zs ihz =>
      induction ys with
      | nil => sorry
      | cons y ys ihy =>
        simp only [levenshteinDistance_cons_cons x xs y ys]
        rw [←min_add_add_right, ←min_add_add_right]
        simp only [le_min_iff]
        refine ⟨?_, ?_, ?_⟩
        · simp only [levenshteinDistance_cons_cons x xs z zs]
          apply min_le_of_left_le
          rw [add_assoc]
          exact add_le_add_left (ihx (y :: ys) (z :: zs)) (delete x)
        · simp only [levenshteinDistance_cons_cons y ys z zs]
          rw [←min_add_add_left, ←min_add_add_left]
          simp only [le_min_iff]
          refine ⟨?_, ?_, ?_⟩
          · sorry -- easy
          · simp only [levenshteinDistance_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_left_le
            rw [add_left_comm]
            apply add_le_add_left
            refine (ihz ys).trans ?_
            rw [add_comm (insert y), add_assoc]
            apply add_le_add_left
            sorry -- doable, maybe warrants a lemma
          · simp only [levenshteinDistance_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_left_le
            sorry -- easy, although needs another hypothesis!
        · simp only [levenshteinDistance_cons_cons y ys z zs]
          rw [←min_add_add_left, ←min_add_add_left]
          simp only [le_min_iff]
          refine ⟨?_, ?_, ?_⟩
          · sorry -- easy
          · simp only [levenshteinDistance_cons_cons x xs z zs]
            apply min_le_of_right_le
            apply min_le_of_left_le
            rw [add_left_comm]
            apply add_le_add_left
            refine (ihz (y :: ys)).trans ?_
            apply add_le_add_right
            sorry -- easy
          · sorry -- easy




theorem List.minimum_le_minimum [LinearOrder α]
    (L M : List α) (w : ∀ m, m ∈ M → ∃ l, l ∈ L ∧ l ≤ m) :
    L.minimum ≤ M.minimum :=
  sorry

theorem levenshteinSuffixDistance_impl_minimum_le [AddZeroClass δ] [LinearOrder δ]
    (delete insert : α → δ) (substitute : α → α → δ) (xs y d) :
    d.1.minimum ≤
      (levenshteinSuffixDistances_impl delete insert substitute xs y d).1.minimum := by
  apply List.minimum_le_minimum
  intro b h
  -- some work to do here, as we need to follow the minimums!
  sorry

variable [AddZeroClass δ] [LinearOrder δ]

theorem levenshteinSuffixDistances_minimum_monotone (delete insert : α → δ) (substitute : α → α → δ)
    (xs : List α) (y : α) (ys : List α) :
    (levenshteinSuffixDistances delete insert substitute xs ys).1.minimum ≤
      (levenshteinSuffixDistances delete insert substitute xs (y :: ys)).1.minimum := by
  dsimp [levenshteinSuffixDistances]
  generalize List.foldr _ _ _ = L
  apply levenshteinSuffixDistance_impl_minimum_le

theorem levenshteinSuffixDistances_minimum_le (delete insert : α → δ) (substitute : α → α → δ) (xs ys zs : List α) :
    (levenshteinSuffixDistances delete insert substitute xs zs).1.minimum ≤
      levenshteinDistance delete insert substitute xs (ys ++ zs) :=
  sorry



#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "".toList |>.1
#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "g".toList |>.1
#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "ng".toList |>.1
#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "sitting".toList |>.1

#eval levenshteinDistance (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "the cat sat on the mat".toList "would you like to play a game?".toList

def string1 := ", ".intercalate (List.replicate 100 "hello")
def string2 := ", ".intercalate (List.replicate 25 "this is just a test")

#eval levenshteinDistance (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) string1.toList string2.toList
