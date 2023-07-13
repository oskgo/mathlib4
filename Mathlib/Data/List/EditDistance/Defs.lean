import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Abel

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

variable {α δ : Type _}

section AddZeroClass
variable [AddZeroClass δ]

section Min
variable [Min δ]

namespace Levenshtein

structure Cost (α β : Type _) (δ : Type _) where
  delete : α → δ
  insert : β → δ
  substitute : α → β → δ

def default [DecidableEq α] : Cost α α ℕ :=
  ⟨fun _ => 1, fun _ => 1, fun a b => if a = b then 0 else 1⟩

instance [DecidableEq α] : Inhabited (Cost α α ℕ) := ⟨default⟩


@[simp] lemma decidableEqDelete [DecidableEq α] (a : α) : default.delete a = 1 := rfl
@[simp] lemma decidableEqInsert [DecidableEq α] (a : α) : default.insert a = 1 := rfl
@[simp] lemma decidableEqSubstitute [DecidableEq α] (a b : α) :
    default.substitute a b = if a = b then 0 else 1 := rfl

variable (C : Cost α β δ)

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
    (xs : List α) (y : β) (d : Σ' (r : List δ), 0 < r.length) : Σ' (r : List δ), 0 < r.length :=
  let ⟨ds, w⟩ := d
  xs.zip (ds.zip ds.tail) |>.foldr
    (init := ⟨[C.insert y + ds.getLast (List.length_pos.mp w)], by simp⟩)
    (fun ⟨x, d₀, d₁⟩ ⟨r, w⟩ =>
      ⟨min (C.delete x + r[0]) (min (C.insert y + d₀) (C.substitute x y + d₁)) :: r, by simp⟩)

variable {C}

-- Note this lemma has an unspecified proof `w'` on the right-hand-side,
-- which will become an extra goal when rewriting.
theorem impl_cons
    (x) (xs) (y) (d) (ds) (w) (w') :
    impl C (x :: xs) y ⟨d :: ds, w⟩ =
      let ⟨r, w⟩ := impl C xs y ⟨ds, w'⟩
      ⟨min
        (C.delete x + r[0])
        (min
          (C.insert y + d)
          (C.substitute x y + ds[0])) :: r, by simp⟩ :=
  match ds, w' with | _ :: _, _ => rfl

theorem impl_cons_fst_zero
    (x) (xs) (y) (d) (ds) (w) (h) (w') :
    (impl C (x :: xs) y ⟨d :: ds, w⟩).1[0] =
      let ⟨r, w⟩ := impl C xs y ⟨ds, w'⟩
      min
        (C.delete x + r[0])
        (min
          (C.insert y + d)
          (C.substitute x y + ds[0])) :=
  match ds, w' with | _ :: _, _ => rfl

theorem impl_length
    (xs) (y) (d) (w : d.1.length = xs.length + 1) :
    (impl C xs y d).1.length =
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

variable (C : Cost α β δ)

/--
`suffixLevenshtein x y` computes the Levenshtein distance
(using the cost functions provided by a `Cost α β δ`)
from each suffix of the list `x` to the list `y`.

The first element of this list is the Levenshtein distance from `x` to `y`.

Note that if the cost functions do not satisfy the inequalities
* `Cost.delete a + Cost.insert b ≥ Cost.substitute a b`
* `Cost.substitute a b + Cost.substitute b c ≥ Cost.substitute a c`
(or if any values are negative)
then the edit distances calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def suffixLevenshtein (xs : List α) (ys : List β) :
    Σ' (r : List δ), 0 < r.length :=
  ys.foldr
    (impl C xs)
    (xs.foldr (init := ⟨[0], by simp⟩) (fun a ⟨r, w⟩ => ⟨(C.delete a + r[0]) :: r, by simp⟩))

variable {C}

theorem suffixLevenshtein_length
    (xs : List α) (ys : List β) :
    (suffixLevenshtein C xs ys).1.length = xs.length + 1 := by
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
theorem suffixLevenshtein_eq (xs : List α) (y ys) (w : d = suffixLevenshtein C xs ys) :
    impl C xs y d = suffixLevenshtein C xs (y :: ys) := by
  subst d
  rfl

variable (C)

/--
`levenshtein x y` computes the Levenshtein distance
(using the cost functions provided by an instance `Cost α β δ`)
from the list `x` to the list `y`.

Note that if the cost functions do not satisfy the inequalities
* `Cost.delete a + Cost.insert b ≥ Cost.substitute a b`
* `Cost.substitute a b + Cost.substitute b c ≥ Cost.substitute a c`
(or if any values are negative)
then the edit distance calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshtein (xs : List α) (ys : List β) : δ :=
  let ⟨r, w⟩ := suffixLevenshtein C xs ys
  r[0]

variable {C}

theorem suffixLevenshtein_nil_nil : (suffixLevenshtein C [] []).1 = [0] := by
  rfl

-- FIXME, find home
theorem List.eq_of_length_one (x : List α) (w : x.length = 1) :
    have : 0 < x.length := (lt_of_lt_of_eq zero_lt_one w.symm)
    x = [x[0]] := by
  match x, w with
  | [r], _ => rfl

theorem suffixLevenshtein_nil' (ys : List β) :
    (suffixLevenshtein C [] ys).1 = [levenshtein C [] ys] :=
  List.eq_of_length_one _ (suffixLevenshtein_length [] _)

theorem suffixLevenshtein_cons₂ (xs : List α) (y ys) :
    suffixLevenshtein C xs (y :: ys) = (impl C xs) y (suffixLevenshtein C xs ys) :=
  rfl

theorem ext_helper {x y : Σ' (r : List β), 0 < r.length}
    (w₀ : x.1[0]'x.2 = y.1[0]'y.2) (w : x.1.tail = y.1.tail) : x = y := by
  match x, y with
  | ⟨hx :: tx, _⟩, ⟨hy :: ty, _⟩ => simp_all

theorem suffixLevenshtein_cons₁
    (x : α) (xs ys) :
    suffixLevenshtein C (x :: xs) ys =
      ⟨levenshtein C (x :: xs) ys ::
        (suffixLevenshtein C xs ys).1, by simp⟩ := by
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
    (suffixLevenshtein C (x :: xs) ys).1 =
      levenshtein C (x :: xs) ys ::
        (suffixLevenshtein C xs ys).1 := by
  simp [suffixLevenshtein_cons₁]

theorem suffixLevenshtein_cons_cons_fst_get_zero
    (x : α) (xs y ys) (w) :
    (suffixLevenshtein C (x :: xs) (y :: ys)).1[0] =
      let ⟨dx, _⟩ := suffixLevenshtein C xs (y :: ys)
      let ⟨dy, _⟩ := suffixLevenshtein C (x :: xs) ys
      let ⟨dxy, _⟩ := suffixLevenshtein C xs ys
      min
        (C.delete x + dx[0])
        (min
          (C.insert y + dy[0])
          (C.substitute x y + dxy[0])) := by
  conv =>
    lhs
    dsimp only [suffixLevenshtein_cons₂]
  simp only [suffixLevenshtein_cons₁]
  rw [impl_cons_fst_zero]
  rfl

theorem suffixLevenshtein_eq_tails_map (xs ys) :
    (suffixLevenshtein C xs ys).1 = xs.tails.map fun xs' => levenshtein C xs' ys := by
  induction xs
  · case nil =>
    simp only [List.map, suffixLevenshtein_nil']
  · case cons x xs ih =>
    simp only [List.map, suffixLevenshtein_cons₁, ih]

@[simp]
theorem levenshtein_nil_nil : levenshtein C [] [] = 0 := by
  simp [levenshtein]

@[simp]
theorem levenshtein_nil_cons (y) (ys) :
    levenshtein C [] (y :: ys) = C.insert y + levenshtein C [] ys := by
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
    levenshtein C (x :: xs) [] = C.delete x + levenshtein C xs [] :=
  rfl

@[simp]
theorem levenshtein_cons_cons
    (x : α) (xs : List α) (y : β) (ys : List β) :
    levenshtein C (x :: xs) (y :: ys) =
      min (C.delete x + levenshtein C xs (y :: ys))
        (min (C.insert y + levenshtein C (x :: xs) ys)
          (C.substitute x y + levenshtein C xs ys)) :=
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


#eval suffixLevenshtein Levenshtein.default "kitten".toList "".toList |>.1
#eval suffixLevenshtein Levenshtein.default "kitten".toList "g".toList |>.1
#eval suffixLevenshtein Levenshtein.default "kitten".toList "ng".toList |>.1
#eval suffixLevenshtein Levenshtein.default "kitten".toList "sitting".toList |>.1

#eval levenshtein Levenshtein.default "the cat sat on the mat".toList "would you like to play a game?".toList

def string1 := ", ".intercalate (List.replicate 100 "hello")
def string2 := ", ".intercalate (List.replicate 25 "this is just a test")

#eval levenshtein Levenshtein.default string1.toList string2.toList
