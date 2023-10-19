import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex


-- See: https://github.com/leanprover/lean4/issues/2220
local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open MeasureTheory MeasureTheory.Measure BigOperators

theorem Measurable.finset_sum' {M α ι : Type*} [MeasurableSpace M] [AddCommMonoid M]
    [MeasurableSpace α] [MeasurableAdd₂ M] (s : Finset ι) {f : ι → α → M}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∑ i in s, f i) :=
  Finset.sum_induction f (fun g => Measurable g) (fun _ _ => Measurable.add') measurable_zero hf

theorem Measurable.finset_sum {M α ι : Type*} [MeasurableSpace M] [AddCommMonoid M]
    [MeasurableSpace α] [MeasurableAdd₂ M] (s : Finset ι) {f : ι → α → M}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x => ∑ i in s, f i x) := by
  simpa only [← Finset.sum_apply] using Measurable.finset_sum' s hf

theorem Measurable.finset_prod' {M α ι : Type*} [MeasurableSpace M] [CommMonoid M]
    [MeasurableSpace α] [MeasurableMul₂ M] (s : Finset ι) {f : ι → α → M}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (∏ i in s, f i) :=
  Finset.prod_induction f (fun g => Measurable g) (fun _ _ => Measurable.mul') measurable_one hf

theorem Measurable.finset_prod {M α ι : Type*} [MeasurableSpace M] [CommMonoid M]
    [MeasurableSpace α] [MeasurableMul₂ M] (s : Finset ι) {f : ι → α → M}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun x => ∏ i in s, f i x) := by
  simpa only [← Finset.prod_apply] using Measurable.finset_prod' s hf

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

theorem MeasureTheory.MeasurePreserving.integral_comp' {α β G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α ≃ᵐ β} (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _

open Set BigOperators Fintype

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

theorem MeasureTheory.lintegral.fin_prod_eq_pow {n : ℕ} (hn : 1 ≤ n) {f : ℝ → ENNReal}
    (hf : Measurable f) : ∫⁻ x : Fin n → ℝ, ∏ i, f (x i) = (∫⁻ x, f x) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [← (volume_preserving_funUnique (Fin 1) ℝ).lintegral_comp hf]
      simp [Nat.zero_eq, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
        MeasurableEquiv.funUnique_apply, pow_one]
  | succ n _ n_ih =>
      have h_mes : ∀ n, Measurable (fun (y : Fin n → ℝ) => ∏ i : Fin n, f (y i)) :=
        fun _ => Measurable.finset_prod Finset.univ (fun i _ => hf.comp (measurable_pi_apply i))
      calc
        _ = ∫⁻ x : ℝ × (Fin n → ℝ), (f x.1) * ∏ i : Fin n, f (x.2 i) := by
          rw [← ((volume_preserving_piFinSuccAboveEquiv _ 0).symm).lintegral_comp (h_mes _)]
          simp_rw [MeasurableEquiv.piFinSuccAboveEquiv_symm_apply, Fin.insertNth_zero',
            Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        _ = (∫⁻ x, f x) * (∫⁻ x, f x) ^ n := by
          rw [volume_eq_prod, lintegral_prod, ← lintegral_mul_const _ hf]
          simp_rw [lintegral_const_mul _ (h_mes _), n_ih]
          refine (hf.aemeasurable.comp_measurable measurable_fst).mul ?_
          exact Measurable.aemeasurable ((h_mes _).comp (f := fun x : _ × _ => x.2) measurable_snd)
        _ = (∫⁻ x, f x) ^ n.succ := by rw [← pow_succ]

theorem MeasureTheory.lintegral.prod_eq_pow {ι : Type*} [Fintype ι] [Nonempty ι] {f : ℝ → ENNReal}
    (hf : Measurable f) :
    ∫⁻ x : ι → ℝ, ∏ i, f (x i) = (∫⁻ x, f x) ^ (card ι) := by
  let s := MeasurableEquiv.piCongrLeft (fun _ => ℝ) (equivFin ι)
  have : MeasurePreserving s.symm := by exact?
  have := MeasurePreserving.lintegral_comp this (f := fun x => ∏ i, f (x i)) ?_
  rw [← this]
  have t1 := fun x : Fin (card ι) → ℝ => Fintype.prod_equiv (equivFin ι)
    (fun i => f ((s.symm x) i)) (fun i => f (x i)) ?_
  simp_rw [t1]
  have : card ι ≠0  := by exact card_ne_zero
  have : 1 ≤ card ι := by exact Nat.one_le_iff_ne_zero.mpr this
  have := MeasureTheory.lintegral.fin_prod_eq_pow this hf
  rw [this]
  intro x
  exact rfl
  refine Measurable.finset_prod _ ?_
  intro _ _
  refine Measurable.comp hf ?_
  exact measurable_pi_apply _




  sorry

#exit

variable (ι : Type*) [Fintype ι]

theorem Pi.integral_iterated_same {E : Type*} [NormedAddCommGroup E] [CommMonoid E]
    [NormedSpace ℝ E] [MeasureSpace E] (f : E → E) :
    ∫ x : ι → E, ∏ i : ι, f (x i) = (∫ x, f x) ^ (card ι) := by
  sorry

variable [Nontrivial ι]

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
  have := Pi.integral_iterated_same ι fun x : ℝ => Real.exp (- x ^ 2)
  rw [this] at t1
  have := integral_gaussian 1
  rw? at t1



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
