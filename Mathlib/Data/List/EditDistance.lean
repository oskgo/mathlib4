import Mathlib.Order.CompleteLattice
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Linarith

@[simp] theorem Array.size_append (x y : Array α) : (x ++ y).size = x.size + y.size := sorry
@[simp] theorem Subarray.size_toSubarray_fin (x : Array α) (i : Fin (x.size + 1)) : x[:i].size = i := sorry
@[simp] theorem Array.size_ofSubarray (x : Subarray α) : Array.size (.ofSubarray x) = x.size := sorry

variable (cost : Array α → Array α → β) [InfSet β] [Add β]

def editDistance' (x y : Array α) : β :=
  ⨅ (x₁) (x₂) (y₁) (y₂) (_ : x = x₁ ++ x₂) (_ : y = y₁ ++ y₂),
    if x₁.size + y₁.size < x.size + y.size then
      editDistance' x₁ y₁ + cost x₂ y₂
    else
      cost x y
termination_by editDistance' x y => x.size + y.size

variable [Min β]

/-- A computable, but completely unoptimized, definition of the (generalized) edit distance. -/
def editDistance (x y : Array α) : β := Id.run do
  let mut b := cost x y
  for i in List.finRange (x.size + 1) do
    for j in List.finRange (y.size + 1) do
      if h : (i + j : ℕ) < x.size + y.size then
        have : Array.size (x[:i] : Array α) + Array.size (y[:j] : Array α) < x.size + y.size :=
          by simpa using h
        b := min b (editDistance x[:i] y[:j] + cost x[i:] y[j:])
      else
        continue
  return b
termination_by editDistance x y => x.size + y.size


section

variable [Zero β] [Top β]

def generalizedLevenshteinCost (insert delete : α → β) (substitute : α → α → β) (x y : Array α) :=
  match x, y with
  | #[], #[] => (0 : β)
  | #[], #[a] => insert a
  | #[a], #[] => delete a
  | #[a], #[b] => substitute a b
  | _, _ => ⊤

variable [One β] [DecidableEq α]

def levenshteinCost : Array α → Array α → β :=
  generalizedLevenshteinCost (fun _ => (1 : β)) (fun _ => (1 : β))
    (fun a b => if a = b then 0 else 1)

end

#eval (editDistance levenshteinCost #["k", "i", "t", "t", "e", "n"] #["s", "i", "t", "t", "i", "n", "g"] : WithTop ℕ)
