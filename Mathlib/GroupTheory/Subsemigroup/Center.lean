/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.Subsemigroup.Operations
import Mathlib.Tactic.LibrarySearch

#align_import group_theory.subsemigroup.center from "leanprover-community/mathlib"@"1ac8d4304efba9d03fa720d06516fac845aa5353"

/-!
# Centers of magmas and semigroups

## Main definitions

* `Set.center`: the center of a magma
* `Subsemigroup.center`: the center of a semigroup
* `Set.addCenter`: the center of an additive magma
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
-/


variable {M : Type*}

namespace Set

/-- Conditions for an element to be additively central -/
structure IsAddCentral [Add M] (z : M) : Prop where
  /-- addition commutes -/
  comm (a : M) : z + a = a + z
  /-- associative property for left addition -/
  left_assoc (b c : M) : z + (b + c) = (z + b) + c
  /-- middle associative addition property -/
  mid_assoc (a c : M) : (a + z) + c = a + (z + c)
  /-- associative property for right addition -/
  right_assoc (a b : M) : (a + b) + z = a + (b + z)

/-- Conditions for an element to be multiplicatively central -/
@[to_additive]
structure IsMulCentral [Mul M] (z : M) : Prop where
  /-- multiplication commutes -/
  comm (a : M): z * a = a * z
  /-- associative property for left multiplication -/
  left_assoc (b c : M) : z * (b * c) = (z * b) * c
  /-- middle associative multiplication property -/
  mid_assoc (a c : M) : (a * z) * c = a * (z * c)
  /-- associative property for right multiplication -/
  right_assoc (a b : M) : (a * b) * z = a * (b * z)

variable (M)

/-- The center of a magma. -/
@[to_additive addCenter " The center of an additive magma. "]
def center [Mul M] : Set M :=
   { z | (IsMulCentral z) }
#align set.center Set.center
#align set.add_center Set.addCenter

-- porting note: The `to_additive` version used to be `mem_addCenter` without the iff
@[to_additive mem_addCenter_iff]
theorem mem_center_iff [Mul M] {z : M} : z ∈ center M ↔ IsMulCentral z :=
  Iff.rfl
#align set.mem_center_iff Set.mem_center_iff
#align set.mem_add_center Set.mem_addCenter_iff

variable {M}

@[to_additive]
theorem _root_.Semigroup.mem_center_iff [Semigroup M] {z : M} :
    z ∈ Set.center M ↔ ∀ g, g * z = z * g := by
  constructor
  · exact fun a g ↦ by rw [Set.IsMulCentral.comm a g]
  · intro h
    constructor
    · intro _
      rw [h]
    · intros _ _
      rw [mul_assoc]
    · intros _ _
      rw [mul_assoc]
    · intros _ _
      rw [mul_assoc]

variable (M)

-- TODO Add `instance : Decidable (IsMulCentral a)` for `instance decidableMemCenter [Mul M]`
instance decidableMemCenter [Semigroup M] [∀ a : M, Decidable <| ∀ b : M, b * a = a * b] :
    DecidablePred (· ∈ center M) := fun _ => decidable_of_iff' _ (Semigroup.mem_center_iff)
#align set.decidable_mem_center Set.decidableMemCenter

@[to_additive (attr := simp) zero_mem_addCenter]
theorem one_mem_center [MulOneClass M] : (1 : M) ∈ Set.center M where
  comm _  := by rw [one_mul, mul_one]
  left_assoc _ _ := by rw [one_mul, one_mul]
  mid_assoc _ _ := by rw [mul_one, one_mul]
  right_assoc _ _ := by rw [mul_one, mul_one]
#align set.one_mem_center Set.one_mem_center
#align set.zero_mem_add_center Set.zero_mem_addCenter

@[simp]
theorem zero_mem_center [MulZeroClass M] : (0 : M) ∈ Set.center M where
  comm _ := by rw [zero_mul, mul_zero]
  left_assoc _ _ := by rw [zero_mul, zero_mul, zero_mul]
  mid_assoc _ _ := by rw [mul_zero, zero_mul, mul_zero]
  right_assoc _ _ := by rw [mul_zero, mul_zero, mul_zero]
#align set.zero_mem_center Set.zero_mem_center

variable {M}

@[to_additive (attr := simp) add_mem_addCenter]
theorem mul_mem_center [Mul M] {z₁ z₂ : M} (hz₁ : z₁ ∈ Set.center M) (hz₂ : z₂ ∈ Set.center M) :
    z₁ * z₂ ∈ Set.center M where
  comm a := calc
    z₁ * z₂ * a = z₂ * z₁ * a := by rw [hz₁.comm]
    _ = z₂ * (z₁ * a) := by rw [hz₁.mid_assoc z₂]
    _ = (a * z₁) * z₂ := by rw [hz₁.comm, hz₂.comm]
    _ = a * (z₁ * z₂) := by rw [hz₂.right_assoc a z₁]
  left_assoc (b c : M) := calc
    z₁ * z₂ * (b * c) = z₁ * (z₂ * (b * c)) := by rw [hz₂.mid_assoc]
    _ = z₁ * ((z₂ * b) * c) := by rw [hz₂.left_assoc]
    _ = (z₁ * (z₂ * b)) * c := by rw [hz₁.left_assoc]
    _ = z₁ * z₂ * b * c := by rw [hz₂.mid_assoc]
  mid_assoc (a c : M) := calc
    a * (z₁ * z₂) * c = ((a * z₁) * z₂) * c := by rw [hz₁.mid_assoc]
    _ = (a * z₁) * (z₂ * c) := by rw [hz₂.mid_assoc]
    _ = a * (z₁ * (z₂ * c)) := by rw [hz₁.mid_assoc]
    _ = a * (z₁ * z₂ * c) := by rw [hz₂.mid_assoc]
  right_assoc (a b : M) := calc
    a * b * (z₁ * z₂) = ((a * b) * z₁) * z₂ := by rw [hz₂.right_assoc]
    _ = (a * (b * z₁)) * z₂ := by rw [hz₁.right_assoc]
    _ =  a * ((b * z₁) * z₂) := by rw [hz₂.right_assoc]
    _ = a * (b * (z₁ * z₂)) := by rw [hz₁.mid_assoc]
#align set.mul_mem_center Set.mul_mem_center
#align set.add_mem_add_center Set.add_mem_addCenter

@[to_additive (attr := simp) neg_mem_addCenter]
theorem inv_mem_center [Group M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [← inv_inj, mul_inv_rev, inv_inv, ha.comm, mul_inv_rev, inv_inv]
#align set.inv_mem_center Set.inv_mem_center
#align set.neg_mem_add_center Set.neg_mem_addCenter

@[simp]
theorem add_mem_center [Distrib M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a + b ∈ Set.center M  where
  comm _ := by rw [add_mul, mul_add, ha.comm, hb.comm]
  left_assoc _ _ := by rw [add_mul, ha.left_assoc, hb.left_assoc, ←add_mul, ←add_mul]
  mid_assoc _ _ := by rw [mul_add, add_mul, ha.mid_assoc, hb.mid_assoc, ←mul_add, ←add_mul]
  right_assoc _ _ := by rw [mul_add, ha.right_assoc, hb.right_assoc, ←mul_add, ←mul_add]
#align set.add_mem_center Set.add_mem_center

@[simp]
theorem neg_mem_center [NonUnitalNonAssocRing M] {a : M} (ha : a ∈ Set.center M) :
    -a ∈ Set.center M where
  comm _ := by rw [← neg_mul_comm, ← ha.comm, neg_mul_comm]
  left_assoc _ _ := by rw [neg_mul, ha.left_assoc, neg_mul, neg_mul]
  mid_assoc _ _ := by rw [← neg_mul_comm, ha.mid_assoc, neg_mul_comm, neg_mul]
  right_assoc _ _ := by rw [mul_neg, ha.right_assoc, mul_neg, mul_neg]
#align set.neg_mem_center Set.neg_mem_centerₓ

@[to_additive subset_addCenter_add_units]
theorem subset_center_units [Monoid M] : ((↑) : Mˣ → M) ⁻¹' center M ⊆ Set.center Mˣ :=
  fun a ha => by
  rw [_root_.Semigroup.mem_center_iff]
  intro _
  rw [←Units.eq_iff, Units.val_mul, Units.val_mul, ha.comm]
#align set.subset_center_units Set.subset_center_units
#align set.subset_add_center_add_units Set.subset_addCenter_add_units

theorem center_units_subset [GroupWithZero M] : Set.center Mˣ ⊆ ((↑) : Mˣ → M) ⁻¹' center M :=
  fun a ha => by
    rw [mem_preimage, _root_.Semigroup.mem_center_iff]
    intro b
    obtain rfl | hb := eq_or_ne b 0
    · rw [zero_mul, mul_zero]
    · exact Units.ext_iff.mp (ha.comm (Units.mk0 b hb)).symm
#align set.center_units_subset Set.center_units_subset

/-- In a group with zero, the center of the units is the preimage of the center. -/
theorem center_units_eq [GroupWithZero M] : Set.center Mˣ = ((↑) : Mˣ → M) ⁻¹' center M :=
  Subset.antisymm center_units_subset subset_center_units
#align set.center_units_eq Set.center_units_eq

@[simp]
theorem inv_mem_center₀ [GroupWithZero M] {a : M} (ha : a ∈ Set.center M) : a⁻¹ ∈ Set.center M := by
  obtain rfl | ha0 := eq_or_ne a 0
  · rw [inv_zero]
    exact zero_mem_center M
  rcases IsUnit.mk0 _ ha0 with ⟨a, rfl⟩
  rw [← Units.val_inv_eq_inv_val]
  exact center_units_subset (inv_mem_center (subset_center_units ha))
#align set.inv_mem_center₀ Set.inv_mem_center₀

@[to_additive (attr := simp) sub_mem_addCenter]
theorem div_mem_center [Group M] {a b : M} (ha : a ∈ Set.center M) (hb : b ∈ Set.center M) :
    a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center hb)
#align set.div_mem_center Set.div_mem_center
#align set.sub_mem_add_center Set.sub_mem_addCenter

@[simp]
theorem div_mem_center₀ [GroupWithZero M] {a b : M} (ha : a ∈ Set.center M)
    (hb : b ∈ Set.center M) : a / b ∈ Set.center M := by
  rw [div_eq_mul_inv]
  exact mul_mem_center ha (inv_mem_center₀ hb)
#align set.div_mem_center₀ Set.div_mem_center₀

variable (M)

@[to_additive (attr := simp) addCenter_eq_univ]
theorem center_eq_univ [CommSemigroup M] : center M = Set.univ :=
  (Subset.antisymm (subset_univ _)) (by
    intros _ _
    rw [_root_.Semigroup.mem_center_iff]
    intro _
    rw [mul_comm]
    )
#align set.center_eq_univ Set.center_eq_univ
#align set.add_center_eq_univ Set.addCenter_eq_univ

end Set

namespace Mul

section

variable (M) [Mul M]

/-- The center of a magma `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a magma `M` is the set of elements that commute with everything in `M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center

variable {M}

/-- The center of a magma is commutative. -/
@[to_additive "The center of an additive magma is commutative."]
instance : CommSemigroup (Mul.center M) where
  mul_assoc := fun _ b _ => Subtype.ext <| b.2.mid_assoc _ _
  mul_comm := fun a _ => Subtype.ext <| a.2.comm _

end

end Mul

namespace Subsemigroup

section

variable (M) [Semigroup M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive
      "The center of a semigroup `M` is the set of elements that commute with everything in `M`"]
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center
#align subsemigroup.center Subsemigroup.center
#align add_subsemigroup.center AddSubsemigroup.center

-- porting note: `coe_center` is now redundant
#noalign subsemigroup.coe_center
#noalign add_subsemigroup.coe_center

variable {M}

@[to_additive]
theorem mem_center_iff {z : M} : z ∈ center M ↔ ∀ g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl
#align subsemigroup.mem_center_iff Subsemigroup.mem_center_iff
#align add_subsemigroup.mem_center_iff AddSubsemigroup.mem_center_iff

@[to_additive]
instance decidableMemCenter (a) [Decidable <| ∀ b : M, b * a = a * b] : Decidable (a ∈ center M) :=
  decidable_of_iff' _ Semigroup.mem_center_iff
#align subsemigroup.decidable_mem_center Subsemigroup.decidableMemCenter
#align add_subsemigroup.decidable_mem_center AddSubsemigroup.decidableMemCenter

/-- The center of a semigroup is commutative. -/
@[to_additive "The center of an additive semigroup is commutative."]
instance center.commSemigroup : CommSemigroup (center M) :=
  { MulMemClass.toSemigroup (center M) with mul_comm := fun a _ => Subtype.ext <| a.2.comm _ }
#align subsemigroup.center.comm_semigroup Subsemigroup.center.commSemigroup
#align add_subsemigroup.center.add_comm_semigroup AddSubsemigroup.center.addCommSemigroup

end

section

variable (M) [CommSemigroup M]

@[to_additive (attr := simp)]
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)
#align subsemigroup.center_eq_top Subsemigroup.center_eq_top
#align add_subsemigroup.center_eq_top AddSubsemigroup.center_eq_top

end

end Subsemigroup

-- Guard against import creep
assert_not_exists Finset
