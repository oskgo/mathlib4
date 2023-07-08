/-
Copyright (c) 2023 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot

! This file was ported from Lean 3 source module number_theory.number_field.units
! leanprover-community/mathlib commit 00f91228655eecdcd3ac97a7fd8dbcb139fe990a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.GroupTheory.Torsion
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Units of a number field
We prove results about the group `(𝓞 K)ˣ` of units of the ring of integers `𝓞 K` of a number
field `K`.

## Main results
* `isUnit_iff_norm`: an algebraic integer `x : 𝓞 K` is a unit if and only if `|norm ℚ x| = 1`

## Tags
number field, units
 -/


open scoped NumberField

noncomputable section

open NumberField Units

section Rat

theorem Rat.RingOfIntegers.isUnit_iff {x : 𝓞 ℚ} : IsUnit x ↔ (x : ℚ) = 1 ∨ (x : ℚ) = -1 := by
  simp_rw [(isUnit_map_iff (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) x).symm, Int.isUnit_iff,
    RingEquiv.coe_toRingHom, RingEquiv.map_eq_one_iff, RingEquiv.map_eq_neg_one_iff, ←
    Subtype.coe_injective.eq_iff]; rfl
#align rat.ring_of_integers.is_unit_iff Rat.RingOfIntegers.isUnit_iff

end Rat

variable (K : Type _) [Field K]

section IsUnit

attribute [local instance] NumberField.ringOfIntegersAlgebra

variable {K}

theorem isUnit_iff_norm [NumberField K] {x : 𝓞 K} :
    IsUnit x ↔ |(RingOfIntegers.norm ℚ x : ℚ)| = 1 := by
  convert (RingOfIntegers.isUnit_norm ℚ (F := K)).symm
  rw [← abs_one, abs_eq_abs, ← Rat.RingOfIntegers.isUnit_iff]
#align is_unit_iff_norm isUnit_iff_norm

end IsUnit

namespace NumberField.Units

section coe

/-- The `MonoidHom` from the group of units `(𝓞 K)ˣ` to the field `K`. -/
def coe_to_field : (𝓞 K)ˣ →* K := (Units.coeHom K).comp (map (algebraMap (𝓞 K) K))

theorem coe_to_field_injective : Function.Injective (coe_to_field K) :=
  fun _ _ h => Units.eq_iff.mp (SetCoe.ext h)

/-- There is a natural coercion from `(𝓞 K)ˣ` to `(𝓞 K)` and then from `(𝓞 K)` to `K` but it is
useful to also have a direct one from `(𝓞 K)ˣ` to `K`. -/
instance : Coe (𝓞 K)ˣ K := ⟨coe_to_field K⟩

theorem ext {x y : (𝓞 K)ˣ} : x = y ↔ (x : K) = (y : K) := (coe_to_field_injective K).eq_iff.symm

theorem ne_zero (x : (𝓞 K)ˣ) : (x : K) ≠ 0 :=
  Subtype.coe_injective.ne_iff.mpr (_root_.Units.ne_zero x)

end coe

open NumberField.InfinitePlace

section torsion

/-- The torsion subgroup of the group of units. -/
def torsion : Subgroup (𝓞 K)ˣ := CommGroup.torsion (𝓞 K)ˣ

theorem mem_torsion {x : (𝓞 K)ˣ} [NumberField K] :
    x ∈ torsion K ↔ ∀ w : InfinitePlace K, w x = 1 := by
  rw [eq_iff_eq (x : K) 1, torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
  refine ⟨fun ⟨n, h_pos, h_eq⟩ φ => ?_, fun h => ?_⟩
  · refine norm_map_one_of_pow_eq_one φ.toMonoidHom (k := ⟨n, h_pos⟩) ?_
    rw [PNat.mk_coe, ← map_pow, h_eq, map_one]
  · obtain ⟨n, hn, hx⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ x.val.prop h
    exact ⟨n, hn, by rwa [ext, map_pow, map_one]⟩
end torsion

instance : Nonempty (torsion K) := ⟨1⟩

/-- The torsion subgroup is finite. -/
instance [NumberField K] : Fintype (torsion K) := by
  refine @Fintype.ofFinite _ (Set.finite_coe_iff.mpr ?_)
  refine Set.Finite.of_finite_image ?_ ((coe_to_field_injective K).injOn _)
  refine (Embeddings.finite_of_norm_le K ℂ 1).subset
    (fun a ⟨u, ⟨h_tors, h_ua⟩⟩ => ⟨?_, fun φ => ?_⟩)
  · rw [← h_ua]
    exact u.val.prop
  · rw [← h_ua]
    exact le_of_eq ((eq_iff_eq _ 1).mp ((mem_torsion K).mp h_tors) φ)

/-- The torsion subgroup is cylic. -/
instance [NumberField K] : IsCyclic (torsion K) := subgroup_units_cyclic _

/-- The order of the torsion subgroup as positive integer. -/
def torsion_order [NumberField K] : ℕ+ := ⟨Fintype.card (torsion K), Fintype.card_pos⟩

namespace dirichlet

open scoped Classical BigOperators

variable [NumberField K]

variable {K}

/-- A distinguished infinite place. -/
def w₀ : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some

variable (K)

/-- The logarithmic embedding of the units. -/
def log_embedding (x : (𝓞 K)ˣ) : {w : InfinitePlace K // w ≠ w₀} → ℝ :=
  fun w => mult K w * Real.log (w.val x)

@[simp]
theorem log_embedding_mul (x y : (𝓞 K)ˣ) :
    log_embedding K (x * y) = log_embedding K x + log_embedding K y := by
  simp only [ne_eq, log_embedding, map_mul, map_eq_zero, ne_zero, not_false_eq_true,
    Real.log_mul, mul_add]
  rfl

@[simp]
theorem log_embedding_inv (x : (𝓞 K)ˣ) :
    log_embedding K x⁻¹ = - log_embedding K x := by
  simp only [ne_eq, log_embedding, map_inv, map_inv₀, Real.log_inv, mul_neg]
  rfl

@[simp]
theorem log_embedding_one :
    log_embedding K (1 : (𝓞 K)ˣ) = 0 := by
  simp only [ne_eq, log_embedding, map_one, Real.log_one, mul_zero]
  rfl

@[simp]
theorem log_embedding_component (x : (𝓞 K)ˣ) (w : {w : InfinitePlace K // w ≠ w₀}) :
    (log_embedding K x) w = mult K w * Real.log (w.val x) := rfl

theorem log_embedding_sum_component (x : (𝓞 K)ˣ) :
    ∑ w, log_embedding K x w = - mult K w₀ * Real.log (w₀ (x : K)) := by
  have h := congrArg Real.log (prod_mult_eq_abs_norm K x)
  rw [show |(Algebra.norm ℚ) (x : K)| = 1 from isUnit_iff_norm.mp x.isUnit, Rat.cast_one,
    Real.log_one, Real.log_prod] at h
  · simp_rw [Real.log_pow] at h
    rw [← Finset.insert_erase (Finset.mem_univ w₀), Finset.sum_insert (Finset.not_mem_erase w₀
      Finset.univ), add_comm, add_eq_zero_iff_eq_neg] at h
    convert h using 1
    · refine (Finset.sum_subtype _ (fun w => ?_) (fun w => (mult K w) * (Real.log (w ↑x)))).symm
      exact ⟨Finset.ne_of_mem_erase, fun h => Finset.mem_erase_of_ne_of_mem h (Finset.mem_univ w)⟩
    · norm_num
  · exact fun w _ => pow_ne_zero _ (AbsoluteValue.ne_zero _ (ne_zero K x))

theorem mult_log_place_eq_zero {x : (𝓞 K)ˣ} {w : InfinitePlace K} :
    mult K w * Real.log (w x) = 0 ↔ w.val x = 1 := by
  rw [mul_eq_zero, or_iff_right, Real.log_eq_zero, or_iff_right, or_iff_left]
  · have : 0 ≤ w.val x := AbsoluteValue.nonneg _ _
    linarith
  · simp only [ne_eq, map_eq_zero, ne_zero K x]
  · exact (ne_of_gt (mult_pos K w))

theorem log_embedding_eq_zero_iff (x : (𝓞 K)ˣ) :
    log_embedding K x = 0 ↔ x ∈ torsion K := by
  rw [mem_torsion]
  refine ⟨fun h w => ?_, fun h => ?_⟩
  · by_cases hw : w = w₀
    · suffices - mult K w₀ * Real.log (w₀ (x : K)) = 0 by
        rw [neg_mul, neg_eq_zero, ← hw] at this
        exact (mult_log_place_eq_zero K).mp this
      rw [← log_embedding_sum_component, Finset.sum_eq_zero]
      exact fun w _ => congrFun h w
    · exact (mult_log_place_eq_zero K).mp (congrFun h ⟨w, hw⟩)
  · ext w
    rw [log_embedding_component, h w.val, Real.log_one, mul_zero, Pi.zero_apply]

/-- The lattice formed by the image of the logarithmic embedding. -/
noncomputable def UnitLattice : AddSubgroup ({w : InfinitePlace K // w ≠ w₀} → ℝ) :=
{ carrier := Set.range (log_embedding K)
  add_mem' := fun ⟨x, _⟩ ⟨y, _⟩ => ⟨x * y, by simp_all⟩
  zero_mem' := ⟨1, log_embedding_one K⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x⁻¹, log_embedding_inv K x⟩ }

theorem log_le_of_log_embedding_le' {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖log_embedding K x‖ ≤ r)
    (w : {w : InfinitePlace K // w ≠ w₀}) : |Real.log (w.val x)| ≤ r := by
  lift r to NNReal using hr
  rw [Pi.norm_def] at h
  simp only [ne_eq, log_embedding_component, nnnorm_mul, Real.nnnorm_coe_nat, NNReal.coe_le_coe,
    Finset.sup_le_iff, Finset.mem_univ, forall_true_left, Subtype.forall] at h
  specialize h w.val w.prop
  rw [← mul_le_mul_left (mult_pos K w)]
  rw [← NNReal.coe_le_coe] at h
  have t1 : (r : ℝ) ≤ (mult K w) * r := sorry
  have t2 := h.trans t1
  exact t2

theorem log_le_of_log_embedding_le {r : ℝ} {x : (𝓞 K)ˣ} (hr : 0 ≤ r) (h : ‖log_embedding K x‖ ≤ r)
    (w : InfinitePlace K) : |Real.log (w x)| ≤ (Fintype.card (InfinitePlace K)) * r := by
  sorry


theorem unitLattice_inter_ball_finite (r : ℝ) :
    ((UnitLattice K : Set ({ w : InfinitePlace K // w ≠ w₀} → ℝ)) ∩
      Metric.closedBall 0 r).Finite := by
  obtain hr | hr := lt_or_le r 0
  · convert Set.finite_empty
    rw [Metric.closedBall_eq_empty.mpr hr]
    exact Set.inter_empty _
  · suffices Set.Finite {x : (𝓞 K)ˣ | IsIntegral ℤ (x : K) ∧
      ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ Real.exp ((Fintype.card (InfinitePlace K)) * r)} by
      refine (Set.Finite.image (log_embedding K) this).subset ?_
      rintro _ ⟨⟨x, rfl⟩, hx⟩
      refine ⟨x, ⟨x.val.prop, ?_⟩, rfl⟩
      rw [← le_iff_le]
      intro w
      by_cases hw : w = w₀
      · rw [← Real.log_le_iff_le_exp]

        sorry
      · sorry
    sorry

end dirichlet

end NumberField.Units
