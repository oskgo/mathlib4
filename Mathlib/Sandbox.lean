import Mathlib.MeasureTheory.Constructions.HaarToSphere

open MeasureTheory

-- MeasureTheory.integral_fun_norm_addHaar.{u_2, u_1} {E : Type u_1} [inst✝ : NormedAddCommGroup E]
--   [inst✝¹ : NormedSpace ℝ E] [inst✝² : FiniteDimensional ℝ E] [inst✝³ : MeasurableSpace E]
--   [inst✝⁴ : BorelSpace E]
--   {F : Type u_2} [inst✝⁵ : NormedAddCommGroup F] [inst✝⁶ : NormedSpace ℝ F]
--   [inst✝⁷ : Nontrivial E] (μ : Measure E) [inst✝⁸ : Measure.IsAddHaarMeasure μ] (f : ℝ → F) :
--   ∫ (x : E), f ‖x‖ ∂μ =
--   dim E • ENNReal.toReal (↑↑μ (ball 0 1)) • ∫ (y : ℝ) in Ioi 0, y ^ (dim E - 1) • f y

example : volume (Metric.ball (0:ℂ) 1) = NNReal.pi := by
  have := MeasureTheory.integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun x => Real.exp (- x))
  simp_rw [Complex.finrank_real_complex, smul_eq_mul] at this
  
