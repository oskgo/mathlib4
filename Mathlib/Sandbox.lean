import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex


open MeasureTheory MeasureTheory.Measure

/-- Docstring. -/
protected noncomputable def Complex.polarCoord : LocalHomeomorph ℂ (ℝ × ℝ) :=
  equivRealProdClm.toHomeomorph.toLocalHomeomorph.trans polarCoord

protected theorem Complex.polarCoord_apply (a : ℂ) :
    Complex.polarCoord a = (Complex.abs a, Complex.arg a) := by
  simp_rw [Complex.abs_def, Complex.normSq_apply, ← pow_two]
  rfl

@[simp]
theorem Complex.equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdAddHom.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

@[simp]
theorem Complex.equivRealProdLm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdLm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

@[simp]
theorem Complex.equivRealProdClm_symm_apply (p : ℝ × ℝ) :
    Complex.equivRealProdClm.symm p = p.1 + p.2 * Complex.I := Complex.equivRealProd_symm_apply p

protected theorem Complex.polarCoord_source :
    Complex.polarCoord.source = {a | 0 < a.re} ∪ {a | a.im ≠ 0} := by simp [Complex.polarCoord]

@[simp]
protected theorem Complex.polarCoord_symm_apply (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
  simp [Complex.polarCoord, mul_add, mul_assoc]

theorem Complex.polardCoord_symm_abs (p : ℝ × ℝ) :
    Complex.abs (Complex.polarCoord.symm p) = |p.1| := by simp

alias Complex.polarCoord_target := polarCoord_target

protected theorem Complex.integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℂ → E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding, ← integral_comp_polarCoord_symm]
  rfl

-- MeasureTheory.integral_fun_norm_addHaar.{u_2, u_1} {E : Type u_1} [inst✝ : NormedAddCommGroup E]
--   [inst✝¹ : NormedSpace ℝ E] [inst✝² : FiniteDimensional ℝ E] [inst✝³ : MeasurableSpace E]
--   [inst✝⁴ : BorelSpace E]
--   {F : Type u_2} [inst✝⁵ : NormedAddCommGroup F] [inst✝⁶ : NormedSpace ℝ F]
--   [inst✝⁷ : Nontrivial E] (μ : Measure E) [inst✝⁸ : Measure.IsAddHaarMeasure μ] (f : ℝ → F) :
--   ∫ (x : E), f ‖x‖ ∂μ =
--   dim E • ENNReal.toReal (↑↑μ (ball 0 1)) • ∫ (y : ℝ) in Ioi 0, y ^ (dim E - 1) • f y

open Set

variable {p : ℝ} (hp : 0 < p)

theorem integral_exp_neg_rpow :
    ∫ x in Ioi (0:ℝ), Real.exp (-(x ^ p)) = (1 / p) * Real.Gamma (1 / p) := by
  calc
    _ = ∫ (x : ℝ) in Ioi 0, (|1 / p| * x ^ (1 / p - 1)) • Real.exp (-x ^ (1 / p * p)) := by
        rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp))]
        refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
        rw [← Real.rpow_mul (le_of_lt hx)]
    _ = 1 / p * ∫ (x : ℝ) in Ioi 0, Real.exp (-x) * x ^ (1 / p - 1) := by
        rw [abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp)), ← integral_mul_left]
        refine set_integral_congr measurableSet_Ioi (fun _ _ => ?_)
        rw [one_div_mul_cancel (ne_of_gt hp), smul_eq_mul, Real.rpow_one]
        ring
    _ = _ := by rw [← Real.Gamma_eq_integral (one_div_pos.mpr hp)]

variable (ι : Type*) [Fintype ι] [Nontrivial ι]

example : volume (Metric.ball (0 : EuclideanSpace ℝ ι) 1) = 0 := by
  have t1 := MeasureTheory.integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ ι))
    (fun x => Real.exp (- x ^ (2:ℝ)))
  simp_rw [finrank_euclideanSpace, EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
    Real.sqrt_eq_rpow, ← Real.rpow_mul sorry, one_div, inv_mul_cancel sorry, Real.rpow_one,
    ← Finset.sum_neg_distrib, Real.exp_sum] at t1
  rw [← MeasurePreserving.integral_comp (EuclideanSpace.volume_preserving_measurableEquiv ι).symm
    (MeasurableEquiv.measurableEmbedding _ )] at t1
  simp_rw [Real.rpow_two, smul_eq_mul, nsmul_eq_mul] at t1
  simp_rw [EuclideanSpace.coe_measurableEquiv_symm, WithLp.equiv_symm_pi_apply] at t1
  


  sorry
  exact MeasurableEquiv.measurableEmbedding _
#exit
  have := fun x : PiLp 2 fun _ : ι => ℝ => PiLp.norm_eq_sum sorry x
  simp_rw [this] at t1
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat, sq_abs, smul_eq_mul,
    nsmul_eq_mul] at t1
  simp_rw [← Real.rpow_mul sorry] at t1
  simp only [Real.rpow_two, sq_abs, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    inv_mul_cancel, Real.rpow_one, ge_iff_le] at t1
  simp_rw [← Finset.sum_neg_distrib] at t1
  simp_rw [Real.exp_sum] at t1
  have :
    ∫ x : (ι → ℝ),
      (fun x => Finset.prod Finset.univ fun i : ι => Real.exp (-x i ^ 2)) x = (0:ℝ) := sorry

  sorry




#exit


example : ∫ (x : ℂ), Real.exp (-‖x‖) = 2 * Real.pi := by
  rw [← Complex.integral_comp_polarCoord_symm]
  simp_rw [polarCoord_target, Complex.norm_eq_abs, Complex.polardCoord_symm_abs, smul_eq_mul]
  rw [volume_eq_prod, set_integral_prod]
  simp_rw [integral_const, restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioo,
    sub_neg_eq_add, ← two_mul, ENNReal.toReal_ofReal sorry, integral_smul, smul_eq_mul]
  have : ∫ (a : ℝ) in Set.Ioi 0, a * Real.exp (- a) = 1 := by sorry
  have := Real.Gamma_eq_integral (by norm_num : (0:ℝ) < 2)
  sorry
  sorry


example : volume (Metric.ball (0:ℂ) 1) = NNReal.pi := by
  have := MeasureTheory.integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun x => Real.exp (- x))
  simp_rw [Complex.finrank_real_complex, smul_eq_mul] at this
