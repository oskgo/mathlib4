import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Cdf

open MeasureTheory Real Set Filter

open scoped Topology

namespace ProbabilityTheory

-- anything with weird goals with many ?m.372368, or goal with sorryAx
-- -> expression did not parse correctly for some reason. Add parentheses, check the type of
-- everything

-- typeclass instance problem is stuck, it is often due to metavariables
-- -> not enough arguments, add ?_ after the lemma name until goals appear
-- or specify enough arguments

-- IR check failed at 'Probability.expCdf._elambda_1', error: unknown declaration 'Real.decidableLE'
-- -> add noncomputable

-- todo: have and suffices don't have same syntax without name

-- todo: can't have sorry in an imported file?

/-- The Cdf of the exponential distribution. -/
@[simps] noncomputable
def expCdf (ℓ : ℝ) (hℓ : 0 < ℓ) : StieltjesFunction :=
{ toFun := fun x ↦ if 0 ≤ x then 1 - exp (- ℓ * x) else 0
  mono' := by
    refine fun x y hxy ↦ ?_
    dsimp only
    split_ifs with hx hy h
    . refine sub_le_sub le_rfl (exp_monotone ?_)
      rw [neg_mul, neg_mul]
      refine neg_le_neg (mul_le_mul_of_nonneg_left hxy hℓ.le)
    . exact absurd (hx.trans hxy) hy
    . refine sub_nonneg_of_le (exp_le_one_iff.mpr ?_)
      rw [neg_mul]
      refine neg_nonpos.mpr (mul_nonneg hℓ.le h)
    . exact le_rfl
  right_continuous' := by
    refine fun x ↦ Continuous.continuousWithinAt ?_
    refine Continuous.if_le ?_ continuous_const continuous_const continuous_id ?_
    . continuity
    . rintro x rfl
      simp }

lemma tendsto_expCdf_atBot (ℓ : ℝ) (hℓ : 0 < ℓ) : Tendsto (expCdf ℓ hℓ) atBot (𝓝 0) := by
  refine tendsto_atBot_of_eventually_const (fun i (hi : i ≤ 0) ↦ ?_)
  simp only [expCdf_apply, neg_mul, ite_eq_right_iff]
  intro hi_ge
  have hi_zero : i = 0 := le_antisymm hi hi_ge
  rw [hi_zero]
  simp

lemma tendsto_expCdf_atTop (ℓ : ℝ) (hℓ : 0 < ℓ) : Tendsto (expCdf ℓ hℓ) atTop (𝓝 1) := by
  suffices Tendsto (fun x ↦ 1 - exp (-ℓ * x)) atTop (𝓝 1) by
    refine Tendsto.congr' ?_ this
    rw [EventuallyEq, eventually_atTop]
    refine ⟨0, fun b hb ↦ ?_⟩
    simp [hb]
  rw [← sub_zero 1]
  refine Tendsto.sub ?_ ?_
  . rw [sub_zero]
    exact tendsto_const_nhds
  . refine tendsto_exp_atBot.comp ?_
    refine Tendsto.neg_const_mul_atTop ?_ tendsto_id
    linarith

/-- The exponential distribution. -/
noncomputable def expDistrib (ℓ : ℝ) (hℓ : 0 < ℓ) : Measure ℝ := (expCdf ℓ hℓ).measure

instance (hℓ : 0 < ℓ) : IsProbabilityMeasure (expDistrib ℓ hℓ) :=
  ⟨by rw [expDistrib, StieltjesFunction.measure_univ _ (tendsto_expCdf_atBot _ _)
    (tendsto_expCdf_atTop _ hℓ), sub_zero, ENNReal.ofReal_one]⟩

lemma cdf_expDistrib (ℓ : ℝ) (hℓ : 0 < ℓ) : cdf (expDistrib ℓ hℓ) = expCdf ℓ hℓ :=
  cdf_measure (expCdf ℓ hℓ) (tendsto_expCdf_atBot _ _) (tendsto_expCdf_atTop _ hℓ)

-- todo: f.measure is equal to withDensity of the derivative
lemma expDistrib_eq_withDensity (ℓ : ℝ) (hℓ : 0 < ℓ) :
    expDistrib ℓ hℓ = volume.withDensity
      (fun x ↦ ENNReal.ofReal (if 0 ≤ x then ℓ * exp (- ℓ * x) else 0)) := by
  refine Measure.ext_of_Iic (expDistrib ℓ hℓ) ?_ (fun x ↦ ?_)
  simp only [neg_mul, measurableSet_Iic, withDensity_apply,
    expDistrib, StieltjesFunction.measure_Iic _ (tendsto_expCdf_atBot _ hℓ)]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  . congr
    rw [sub_zero]
    sorry
  . sorry
  . sorry

end ProbabilityTheory
