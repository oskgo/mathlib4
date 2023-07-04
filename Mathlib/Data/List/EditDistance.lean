import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.CategoryTheory.PathCategory
import Mathlib.Data.FinEnum


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

-- def generalizedLevenshteinCost (insert delete : α → β) (substitute : α → α → β) (x y : List α) :=
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


variable [Min β] [AddZeroClass β]

/--
(Implementation detail for `levenshteinDistance`)

Given a list `xs` and the Levenshtein distances from each suffix of `xs` to some other list `ys`,
compute the Levenshtein distances from each suffix of `xs` to `y :: ys`.

(Note that we don't actually need to know `ys` itself here, so it is not an argument.)
-/
def levenshteinSuffixDistances_impl (insert delete : α → β) (substitute : α → α → β)
    (xs : List α) (y : α) (d : Σ' (r : List β), 0 < r.length) : Σ' (r : List β), 0 < r.length :=
  let ⟨ds, w⟩ := d
  xs.zip (ds.zip ds.tail) |>.foldr
    (init := ⟨[ds.getLast (List.length_pos.mp w) + insert y], by simp⟩)
    (fun ⟨x, d₀, d₁⟩ ⟨r, w⟩ =>
      ⟨min (delete x + r[0]) (min (insert y + d₀) (substitute x y + d₁)) :: r, by simp⟩)

/--
`levenshteinSuffixDistances insert delete substitute x y` computes the Levenshtein distance
(using the cost functions `insert delete α → β` and `substitute : α → α → β`)
from each suffix of the list `x` to the list `y`.

The first element of this list is the Levenshtein distance from `x` to `y`.

The return value is a list of length `x.length + 1`,
and it is convenient for the recursive calls that we bundle this list
with a proof that it is non-empty.

Note that if the cost functions do not satisfy the inequalities
* `delete a + insert b ≥ substitute a b`
* `substitute a b + substitute b c ≥ substitute a c`
(or if any values are negative)
then the edit distances calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshteinSuffixDistances (insert delete : α → β) (substitute : α → α → β) (xs ys : List α) :
    Σ' (r : List β), 0 < r.length :=
  ys.foldr
    (levenshteinSuffixDistances_impl insert delete substitute xs)
    (xs.foldr (init := ⟨[0], by simp⟩) (fun a ⟨r, w⟩ => ⟨(delete a + r[0]) :: r, by simp⟩))

/--
`levenshteinDistance insert delete substitute x y` computes the Levenshtein distance
(using the cost functions `insert delete α → β` and `substitute : α → α → β`)
from the list `x` to the list `y`.

Note that if the cost functions do not satisfy the inequalities
* `delete a + insert b ≥ substitute a b`
* `substitute a b + substitute b c ≥ substitute a c`
(or if any values are negative)
then the edit distance calculated here may not agree with the general
geodesic distance on the edit graph.
-/
def levenshteinDistance (insert delete : α → β) (substitute : α → α → β) (x y : List α) : β :=
  let ⟨r, w⟩ := levenshteinSuffixDistances insert delete substitute x y
  r[0]

#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "".toList |>.1
#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "g".toList |>.1
#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "ng".toList |>.1
#eval levenshteinSuffixDistances (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "kitten".toList "sitting".toList |>.1

#eval levenshteinDistance (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) "the cat sat on the mat".toList "would you like to play a game?".toList

def string1 := ", ".intercalate (List.replicate 100 "hello")
def string2 := ", ".intercalate (List.replicate 25 "this is just a test")

#eval levenshteinDistance (fun _ => 1) (fun _ => 1) (fun a b => if a = b then 0 else 1) string1.toList string2.toList
