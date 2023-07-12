import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Abel
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Combinatorics.Quiver.Path
-- import Mathlib.CategoryTheory.PathCategory
-- import Mathlib.Data.FinEnum

/-!
# Levenshtein distances

We define the Levenshtein edit distance `levenshtein` between two `List α`,
with a customizable cost function for the `delete`, `insert`, and `substitute` operations.

As an auxiliary function, we define `suffixLevenshtein xs ys`, which gives the list of distances
from each suffix of `xs` to `ys`.
This is defined by recursion on `ys`, using the internal function `Levenshtein.impl`,
which computes `suffixLevenshtein xs (y :: ys)` using `xs`, `y`, and `suffixLevenshtein xs ys`.
(This corresponds to the usual algorithm
using the last two rows of the matrix of distances between suffixes.)

After setting up these definitions, we prove lemmas specifying their behaviour,
particularly

```
theorem suffixLevenshtein_eq_tails_map :
  (suffixLevenshtein xs ys).1 = xs.tails.map fun xs' => levenshtein xs' ys := ...
```

and

```
theorem levenshtein_cons_cons :
  levenshtein (x :: xs) (y :: ys) =
    min (delete x + levenshtein xs (y :: ys))
      (min (insert y + levenshtein (x :: xs) ys)
        (substitute x y + levenshtein xs ys)) := ...
```

-/

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

variable {α δ : Type _}

section AddZeroClass
variable [AddZeroClass δ]

section Min
variable [Min δ]

namespace Levenshtein

class Cost (α : Type _) (δ : outParam (Type _)) where
  delete : α → δ
  insert : α → δ
  substitute : α → α → δ

instance (priority := low) [DecidableEq α] : Cost α ℕ where
  delete _ := 1
  insert _ := 1
  substitute a b := if a = b then 0 else 1

variable [Cost α δ]

/--
(Implementation detail for `levenshtein`)

Given a list `xs` and the Levenshtein distances from each suffix of `xs` to some other list `ys`,
compute the Levenshtein distances from each suffix of `xs` to `y :: ys`.

(Note that we don't actually need to know `ys` itself here, so it is not an argument.)

The return value is a list of length `x.length + 1`,
and it is convenient for the recursive calls that we bundle this list
with a proof that it is non-empty.
-/
def impl
    (xs : List α) (y : α) (d : Σ' (r : List δ), 0 < r.length) : Σ' (r : List δ), 0 < r.length :=
  let ⟨ds, w⟩ := d
  xs.zip (ds.zip ds.tail) |>.foldr
    (init := ⟨[Cost.insert y + ds.getLast (List.length_pos.mp w)], by simp⟩)
    (fun ⟨x, d₀, d₁⟩ ⟨r, w⟩ =>
      ⟨min (Cost.delete x + r[0]) (min (Cost.insert y + d₀) (Cost.substitute x y + d₁)) :: r, by simp⟩)

-- Note this lemma has an unspecified proof `w'` on the right-hand-side,
-- which will become an extra goal when rewriting.
theorem impl_cons
    (x) (xs : List α) (y) (d) (ds) (w) (w') :
    impl (x :: xs) y ⟨d :: ds, w⟩ =
      let ⟨r, w⟩ := impl xs y ⟨ds, w'⟩
      ⟨min
        (Cost.delete x + r[0])
        (min
          (Cost.insert y + d)
          (Cost.substitute x y + ds[0])) :: r, by simp⟩ :=
  match ds, w' with | _ :: _, _ => rfl

theorem impl_cons_fst_zero
    (x) (xs : List α) (y) (d) (ds) (w) (h) (w') :
    (impl (x :: xs) y ⟨d :: ds, w⟩).1[0] =
      let ⟨r, w⟩ := impl xs y ⟨ds, w'⟩
      min
        (Cost.delete x + r[0])
        (min
          (Cost.insert y + d)
          (Cost.substitute x y + ds[0])) :=
  match ds, w' with | _ :: _, _ => rfl

theorem impl_length
    (xs : List α) (y) (d) (w : d.1.length = xs.length + 1) :
    (impl xs y d).1.length =
      xs.length + 1 := by
  induction xs generalizing d
  · case nil =>
    rfl
  · case cons x xs ih =>
    dsimp [impl]
    match d, w with
    | ⟨d₁ :: d₂ :: ds, _⟩, w =>
      dsimp
      congr 1
      refine ih ⟨d₂ :: ds, (by simp)⟩ (by simpa using w)

end Levenshtein

open Levenshtein

variable [Cost α δ]

/--
`suffixLevenshtein x y` computes the Levenshtein distance
(using the cost functions provided by an instance `Cost α δ`)
from each suffix of the list `x` to the list `y`.

The first element of this list is the Levenshtein distance from `x` to `y`.

Note that if the cost functions do not satisfy the inequalities
* `Cost.delete a + Cost.insert b ≥ Cost.substitute a b`
* `Cost.substitute a b + Cost.substitute b c ≥ Cost.substitute a c`
(or if any values are negative)
then the edit distances calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def suffixLevenshtein (xs : List α) (ys : List α) :
    Σ' (r : List δ), 0 < r.length :=
  ys.foldr
    (impl xs)
    (xs.foldr (init := ⟨[0], by simp⟩) (fun a ⟨r, w⟩ => ⟨(Cost.delete a + r[0]) :: r, by simp⟩))

theorem suffixLevenshtein_length
    (xs : List α) (ys : List α) :
    (suffixLevenshtein xs ys).1.length = xs.length + 1 := by
  induction ys
  · case nil =>
    dsimp [suffixLevenshtein]
    induction xs
    · case nil => rfl
    · case cons _ xs ih =>
      simp_all
  · case cons y ys ih =>
    dsimp [suffixLevenshtein]
    rw [impl_length]
    exact ih

-- This is only used in keeping track of estimates.
theorem suffixLevenshtein_eq (xs : List α) (y ys) (w : d = suffixLevenshtein xs ys) :
    impl xs y d = suffixLevenshtein xs (y :: ys) := by
  subst d
  rfl

/--
`levenshtein x y` computes the Levenshtein distance
(using the cost functions provided by an instance `Cost α δ`)
from the list `x` to the list `y`.

Note that if the cost functions do not satisfy the inequalities
* `Cost.delete a + Cost.insert b ≥ Cost.substitute a b`
* `Cost.substitute a b + Cost.substitute b c ≥ Cost.substitute a c`
(or if any values are negative)
then the edit distance calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshtein (xs : List α) (ys : List α) : δ :=
  let ⟨r, w⟩ := suffixLevenshtein xs ys
  r[0]

theorem suffixLevenshtein_nil_nil : (suffixLevenshtein ([] : List α) []).1 = [0] := by
  rfl

-- FIXME, find home
theorem List.eq_of_length_one (x : List α) (w : x.length = 1) :
    have : 0 < x.length := (lt_of_lt_of_eq zero_lt_one w.symm)
    x = [x[0]] := by
  match x, w with
  | [r], _ => rfl

theorem suffixLevenshtein_nil' (ys : List α) :
    (suffixLevenshtein [] ys).1 = [levenshtein [] ys] :=
  List.eq_of_length_one _ (suffixLevenshtein_length [] _)

theorem suffixLevenshtein_cons₂ (xs : List α) (y ys) :
    suffixLevenshtein xs (y :: ys) = (impl xs) y (suffixLevenshtein xs ys) :=
  rfl

theorem ext_helper {x y : Σ' (r : List β), 0 < r.length}
    (w₀ : x.1[0]'x.2 = y.1[0]'y.2) (w : x.1.tail = y.1.tail) : x = y := by
  match x, y with
  | ⟨hx :: tx, _⟩, ⟨hy :: ty, _⟩ => simp_all

theorem suffixLevenshtein_cons₁
    (x : α) (xs ys) :
    suffixLevenshtein (x :: xs) ys =
      ⟨levenshtein (x :: xs) ys ::
        (suffixLevenshtein xs ys).1, by simp⟩ := by
  induction ys
  · case nil =>
    dsimp [levenshtein, suffixLevenshtein]
  · case cons y ys ih =>
    apply ext_helper
    · rfl
    · rw [suffixLevenshtein_cons₂ (x :: xs), ih, impl_cons]
      · rfl
      · simp [suffixLevenshtein_length]

theorem suffixLevenshtein_cons₁_fst (x : α) (xs ys) :
    (suffixLevenshtein (x :: xs) ys).1 =
      levenshtein (x :: xs) ys ::
        (suffixLevenshtein xs ys).1 := by
  simp [suffixLevenshtein_cons₁]

theorem suffixLevenshtein_cons_cons_fst_get_zero
    (x : α) (xs y ys) (w) :
    (suffixLevenshtein (x :: xs) (y :: ys)).1[0] =
      let ⟨dx, _⟩ := suffixLevenshtein xs (y :: ys)
      let ⟨dy, _⟩ := suffixLevenshtein (x :: xs) ys
      let ⟨dxy, _⟩ := suffixLevenshtein xs ys
      min
        (Cost.delete x + dx[0])
        (min
          (Cost.insert y + dy[0])
          (Cost.substitute x y + dxy[0])) := by
  conv =>
    lhs
    dsimp only [suffixLevenshtein_cons₂]
  simp only [suffixLevenshtein_cons₁]
  rw [impl_cons_fst_zero]
  rfl

theorem suffixLevenshtein_eq_tails_map (xs ys : List α) :
    (suffixLevenshtein xs ys).1 = xs.tails.map fun xs' => levenshtein xs' ys := by
  induction xs
  · case nil =>
    simp only [List.map, suffixLevenshtein_nil']
  · case cons x xs ih =>
    simp only [List.map, suffixLevenshtein_cons₁, ih]

@[simp]
theorem levenshtein_nil_nil : levenshtein ([] : List α) [] = 0 := by
  simp [levenshtein]

@[simp]
theorem levenshtein_nil_cons (y : α) (ys : List α) :
    levenshtein [] (y :: ys) = Cost.insert y + levenshtein [] ys := by
  dsimp [levenshtein]
  congr
  rw [List.getLast_eq_get]
  congr
  rw [show (List.length _) = 1 from _]
  induction ys with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldr]
    rw [impl_length] <;> simp [ih]

@[simp]
theorem levenshtein_cons_nil (x : α) (xs : List α) :
    levenshtein (x :: xs) [] = Cost.delete x + levenshtein xs [] :=
  rfl

@[simp]
theorem levenshtein_cons_cons
    (x : α) (xs : List α) (y : α) (ys : List α) :
    levenshtein (x :: xs) (y :: ys) =
      min (Cost.delete x + levenshtein xs (y :: ys))
        (min (Cost.insert y + levenshtein (x :: xs) ys)
          (Cost.substitute x y + levenshtein xs ys)) :=
  suffixLevenshtein_cons_cons_fst_get_zero _ _ _ _ _

end Min

end AddZeroClass

-- Err... what hypotheses does this need?
-- @[simp]
-- theorem levenshtein_cons_self [LinearOrderedAddCommMonoid δ]
--     {delete : α → δ} {insert : α → δ} {substitute : α → α → δ}
--     (hdelete : ∀ a, 0 ≤ delete a) (hinsert : ∀ a, 0 ≤ insert a)
--     (hsubstitute : ∀ a, substitute a a = 0) (a xs ys) :
--     levenshtein delete insert substitute (a :: xs) (a :: ys) =
--       levenshtein delete insert substitute xs ys := by
--   sorry

namespace Levenshtein

def Cost.Flip (α : Type _) := α

instance [Cost α δ] : Cost (Cost.Flip α) δ where
  insert (a : α) := Cost.delete a
  delete (a : α) := Cost.insert a
  substitute (a b : α) := Cost.substitute b a

def Cost.toFlip (x : α) : Cost.Flip α := x

end Levenshtein

open Levenshtein

variable [Cost α δ]

theorem levenshtein_symm [AddZeroClass δ] [LinearOrder δ]
    (xs : List α) (ys : List α) :
    levenshtein xs ys =
      levenshtein (ys.map Levenshtein.Cost.toFlip) (xs.map Levenshtein.Cost.toFlip) := by
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
      rw [← min_assoc, min_comm (Cost.delete x + _), min_assoc]
      rfl

theorem levenshtein_nonneg [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a : α, 0 ≤ Cost.delete a) (hinsert : ∀ b : α, 0 ≤ Cost.insert b)
    (hsubstitute₁ : ∀ a b : α, 0 ≤ Cost.substitute a b) (xs : List α) (ys : List α) :
    0 ≤ levenshtein xs ys := by
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

theorem levenshtein_refl [LinearOrderedAddCommMonoid δ]
    (hinsert : ∀ a : α , 0 ≤ Cost.insert a) (hdelete : ∀ a : α, 0 ≤ Cost.delete a)
    (hsubstitute₁ : ∀ a b : α, 0 ≤ Cost.substitute a b)
    (hsubstitute₂ : ∀ a : α, Cost.substitute a a = 0)
    (xs : List α) : levenshtein xs xs = 0 := by
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

theorem foo [LinearOrder α] {a b c : α} (w : min a b = c) (h : c < a) : b = c := by
  rw [min_eq_iff] at w
  rcases w with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exfalso; apply lt_irrefl a; exact h
  · rfl

theorem levenshtein_eq_of_zero [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a : α, 0 < Cost.delete a) (hinsert : ∀ a : α, 0 < Cost.insert a)
    (hsubstitute₁ : ∀ a b : α, 0 ≤ Cost.substitute a b) (hsubstitute₂ : ∀ a b : α, Cost.substitute a b = 0 ↔ a = b)
    {xs ys : List α}
    (w : levenshtein xs ys = 0) : xs = ys := by
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
      replace w := foo w ?_
      replace w := foo w ?_
      · replace w : Cost.substitute x y = 0 ∧ levenshtein xs ys = 0 :=
          (add_eq_zero_iff' (hsubstitute₁ x y) (nonneg _ _)).mp w
        rw [hsubstitute₂] at w
        obtain ⟨rfl, w⟩ := w
        congr
        apply ihx w
      · exact add_pos_of_pos_of_nonneg (hinsert _) (nonneg _ _)
      · exact add_pos_of_pos_of_nonneg (hdelete _) (nonneg _ _)


theorem levenshtein_le_insert [LinearOrderedAddCommMonoid δ]
    (hinsert : ∀ a : α, 0 ≤ Cost.insert a) (hdelete : ∀ a : α, 0 ≤ Cost.delete a)
    (x : α) (xs ys) :
    levenshtein xs ys ≤ Cost.insert x + levenshtein (x :: xs) ys := by
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




theorem levenshtein_trans [LinearOrderedAddCommMonoid δ]
    (hinsert : ∀ a : α, 0 ≤ Cost.insert a) (hdelete : ∀ a : α, 0 ≤ Cost.delete a)
    (hsubstitute₁ : ∀ a b : α, 0 ≤ Cost.substitute a b) (hsubstitute₂ : ∀ a : α, Cost.substitute a a = 0)
    (hsubstitute₃ : ∀ a b c : α, Cost.substitute a c ≤ Cost.substitute a b + Cost.substitute b c)
    (xs ys zs : List α) :
    levenshtein xs zs ≤
      levenshtein xs ys +
      levenshtein ys zs := by
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
          exact add_le_add_left (ihx (y :: ys) (z :: zs)) (Cost.delete x)
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
            rw [add_comm (Cost.insert y), add_assoc]
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

theorem levenshtein_bound' [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a : α, 0 ≤ Cost.delete a) (hinsert : ∀ a : α, 0 ≤ Cost.insert a)
    (hsubstitute : ∀ a b : α, 0 ≤ Cost.substitute a b) (xs : List α) (y ys) :
    (suffixLevenshtein xs ys).1.minimum ≤ levenshtein xs (y :: ys) := by
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
        _ ≤ (suffixLevenshtein xs ys).1.minimum := by
            simp [suffixLevenshtein_cons₁_fst, List.minimum_cons]
        _ ≤ ↑(levenshtein xs (y :: ys)) := ih
        _ ≤ _ := by
            simpa using le_add_of_nonneg_left (hdelete x)
    · calc
        (suffixLevenshtein (x :: xs) ys).1.minimum ≤ ↑(levenshtein (x :: xs) ys) := by
            simp [suffixLevenshtein_cons₁_fst, List.minimum_cons]
        _ ≤ _ := by
            simpa using le_add_of_nonneg_left (hinsert y)
    · calc
        (suffixLevenshtein (x :: xs) ys).1.minimum ≤ ↑(levenshtein xs ys) := by
            simp only [suffixLevenshtein_cons₁_fst, List.minimum_cons]
            apply min_le_of_right_le
            cases xs
            · simp [suffixLevenshtein_nil']
            · simp [suffixLevenshtein_cons₁, List.minimum_cons]
        _ ≤ _ := by
            simpa using le_add_of_nonneg_left (hsubstitute x y)

theorem List.minimum_le_coe_iff [LinearOrder α] (L : List α) (a : α) :
    L.minimum ≤ a ↔ ∃ b, b ∈ L ∧ b ≤ a := by
  induction L with
  | nil => simp
  | cons h t ih =>
    simp [List.minimum_cons, ih]

theorem levenshtein_bound [LinearOrderedAddCommMonoid δ]
    (hdelete : ∀ a : α, 0 ≤ Cost.delete a) (hinsert : ∀ a : α, 0 ≤ Cost.insert a)
    (hsubstitute : ∀ a b : α, 0 ≤ Cost.substitute a b) (xs : List α) (y ys) :
    ∃ xs', xs' <:+ xs ∧ levenshtein xs' ys ≤ levenshtein xs (y :: ys) := by
  simpa [suffixLevenshtein_eq_tails_map, List.minimum_le_coe_iff] using
    levenshtein_bound' hdelete hinsert hsubstitute xs y ys

#eval suffixLevenshtein "kitten".toList "".toList |>.1
#eval suffixLevenshtein "kitten".toList "g".toList |>.1
#eval suffixLevenshtein "kitten".toList "ng".toList |>.1
#eval suffixLevenshtein "kitten".toList "sitting".toList |>.1

#eval levenshtein "the cat sat on the mat".toList "would you like to play a game?".toList

def string1 := ", ".intercalate (List.replicate 100 "hello")
def string2 := ", ".intercalate (List.replicate 25 "this is just a test")

#eval levenshtein string1.toList string2.toList
