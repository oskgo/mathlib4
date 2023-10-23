import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.NormedSpace.PiLp

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
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding, ← integral_comp_polarCoord_symm]
  rfl

theorem MeasureTheory.MeasurePreserving.integral_comp' {α β G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    {f : α ≃ᵐ β} (h : MeasurePreserving f μ ν) (g : β → G) :
    ∫ x, g (f x) ∂μ = ∫ y, g y ∂ν := MeasurePreserving.integral_comp h f.measurableEmbedding _

section tools

open Set BigOperators Fintype Asymptotics Filter

variable {p : ℝ}

theorem exp_neg_mul_rpow_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) (hp : 1 < p) :
    (fun x : ℝ => Real.exp (- b * x ^ p)) =o[atTop] fun x : ℝ => Real.exp (-x) := by
  rw [Real.isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun x hx => ?_)
    have hx : x ≠ 0 := by exact ne_of_gt hx
    rw [Real.rpow_sub_one hx]
    field_simp [hx]
    ring
  apply Tendsto.atTop_mul_atTop tendsto_id
  refine tendsto_atTop_add_const_right atTop (-1 : ℝ) ?_
  refine Tendsto.const_mul_atTop hb ?_
  refine tendsto_rpow_atTop ?_
  simp only [sub_pos, hp]

theorem rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg (s : ℝ) {b : ℝ} (hp : 1 < p) (hb : 0 < b) :
    (fun x : ℝ => x ^ s * Real.exp (- b * x ^ p)) =o[atTop]
      fun x : ℝ => Real.exp (-(1 / 2) * x) := by
  apply ((isBigO_refl (fun x : ℝ => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s

theorem integrable_rpow_mul_exp_neg_rpow {q : ℝ} (hq : -1 < q) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ => x ^ q * Real.exp (- x ^ p)) (Ioi 0) := by
  obtain hp | hp := le_iff_lt_or_eq.mp hp
  · have h_exp : ∀ x, ContinuousAt (fun x => Real.exp (- x)) x :=
        fun x => (by exact continuousAt_neg : ContinuousAt (fun x => -x) x).exp
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
    constructor
    · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
      refine IntegrableOn.mul_continuousOn ?_ ?_ isCompact_Icc
      · refine (intervalIntegrable_iff_integrable_Icc_of_le zero_le_one).mp ?_
        exact intervalIntegral.intervalIntegrable_rpow' hq
      · intro x _
        change ContinuousWithinAt ((fun x => Real.exp (- x)) ∘ (fun x => x ^ p)) (Icc 0 1) x
        refine ContinuousAt.comp_continuousWithinAt (h_exp _) ?_
        exact continuousWithinAt_id.rpow_const (Or.inr (le_of_lt (lt_trans zero_lt_one hp)))
    · have h_rpow : ∀ (x r : ℝ), x ∈ Ici 1 → ContinuousWithinAt (fun x => x ^ r) (Ici 1) x := by
        intro _ r hx
        refine continuousWithinAt_id.rpow_const (Or.inl ?_)
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
      refine integrable_of_isBigO_exp_neg (by norm_num : (0:ℝ) < 1 / 2)
        (ContinuousOn.mul (fun x hx => h_rpow x q hx) (fun x hx => ?_)) (IsLittleO.isBigO ?_)
      · change ContinuousWithinAt ((fun x => Real.exp (- x)) ∘ (fun x => x ^ p)) (Ici 1) x
        exact ContinuousAt.comp_continuousWithinAt (h_exp _) (h_rpow x p hx)
      · convert rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg q hp (by norm_num : (0:ℝ) < 1) using 3
        rw [neg_mul, one_mul]
  · simp_rw [← hp, Real.rpow_one]
    convert Real.GammaIntegral_convergent (by linarith : 0 < q + 1) using 2
    rw [add_sub_cancel, mul_comm]

theorem MeasureTheory.integral_comp_abs {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f x) (Ioi 0)) :
    ∫ x, f |x| = 2 • ∫ x in Ioi (0:ℝ), f x := by
  calc
    _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := ?_
    _ = 2 • ∫ x in Ioi 0, f x := ?_
  · have h_int : IntegrableOn (fun x => f |x|) (Ioi 0) := by
      refine IntegrableOn.congr_fun hf (fun _ hx => ?_) measurableSet_Ioi
      rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
    rw [← integral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi, Iic_union_Ioi,
      restrict_univ]
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let A : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).closedEmbedding.measurableEmbedding
    rw [A.integrableOn_map_iff]
    simp only [Function.comp, abs_neg, neg_preimage, preimage_neg_Iic, neg_zero]
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact h_int
    exact h_int
  · rw [two_smul]
    congr! 1
    · rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
      refine set_integral_congr measurableSet_Iic (fun _ hx => ?_)
      rw [abs_eq_neg_self.mpr (by exact hx)]
    · refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
      rw [abs_eq_self.mpr (le_of_lt (by exact hx))]

section p_pos

variable (hp : 0 < p)

theorem integral_rpow_mul_exp_neg_rpow {q : ℝ} (hq : - 1 < q) :
    ∫ x in Ioi (0:ℝ), x ^ q * Real.exp (- x ^ p) = (1 / p) * Real.Gamma ((q + 1) / p) := by
  calc
    _ = ∫ (x : ℝ) in Ioi 0,  (1 / p * x ^ (1 / p - 1)) •
          ((x ^ (1 / p)) ^ q * Real.exp (-x)) := by
      rw [← integral_comp_rpow_Ioi _ (one_div_ne_zero (ne_of_gt hp)),
        abs_eq_self.mpr (le_of_lt (one_div_pos.mpr hp))]
      refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
      rw [← Real.rpow_mul (le_of_lt hx) _ p, one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]
    _ = ∫ (x : ℝ) in Ioi 0, 1 / p * Real.exp (-x) * x ^ (1 / p - 1 + q / p) := by
      simp_rw [smul_eq_mul, mul_assoc]
      refine set_integral_congr measurableSet_Ioi (fun _ hx => ?_)
      rw [← Real.rpow_mul (le_of_lt hx), div_mul_eq_mul_div, one_mul, Real.rpow_add hx]
      ring_nf
    _ = (1 / p) * Real.Gamma ((q + 1) / p) := by
      rw [Real.Gamma_eq_integral (div_pos (neg_lt_iff_pos_add.mp hq) hp)]
      simp_rw [show 1 / p - 1 + q / p = (q + 1) / p - 1 by field_simp; ring, ← integral_mul_left,
        ← mul_assoc]

theorem integral_exp_neg_rpow :
    ∫ x in Ioi (0:ℝ), Real.exp (- x ^ p) = Real.Gamma (1 / p + 1) := by
  convert (integral_rpow_mul_exp_neg_rpow hp neg_one_lt_zero) using 1
  · simp_rw [Real.rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (one_div_ne_zero (ne_of_gt hp))]

theorem Complex.integral_rpow_mul_exp_neg_rpow {q : ℝ} (hq : - 2 < q) :
    ∫ x : ℂ, ‖x‖ ^ q * Real.exp (- ‖x‖ ^ p) = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := by
  calc
    _ = ∫ x in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi, x.1 * (|x.1| ^ q * Real.exp (-|x.1| ^ p)) := ?_
    _ = ∫ (x : ℝ) in Ioi 0, ∫ (y : ℝ) in Ioo (-Real.pi) Real.pi,
          x * |x| ^ q * Real.exp (-|x| ^ p) := ?_
    _ = 2 * Real.pi * ∫ x in Ioi (0:ℝ), x * |x| ^ q * Real.exp (-|x| ^ p) := ?_
    _ = 2 * Real.pi * ∫ x in Ioi (0:ℝ), x ^ (q + 1) * Real.exp (-x ^ p) := ?_
    _ = (2 * Real.pi / p) * Real.Gamma ((q + 2) / p) := ?_
  · rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    simp_rw [Complex.norm_eq_abs, Complex.polardCoord_symm_abs, smul_eq_mul]
  · rw [volume_eq_prod, set_integral_prod]
    simp_rw [mul_assoc]
    -- have := Real.GammaIntegral_convergent
    -- have := integrable_of_isBigO_exp_neg
    rw [integrableOn_def]
    -- rw [integrable_prod_iff]
    -- have : Integrable fun x : ℝ => x * (Real.exp (-|x| ^ p) * |x| ^ q) := sorry
    -- refine Integrable.prod_mul this ?_

    sorry
  · simp_rw [integral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Ioo, sub_neg_eq_add, ← two_mul, ENNReal.toReal_ofReal (by positivity :
      0 ≤ 2 * Real.pi), integral_smul, smul_eq_mul]
  · congr 1
    refine set_integral_congr measurableSet_Ioi (fun x hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx)), Real.rpow_add hx, Real.rpow_one]
    ring
  · rw [_root_.integral_rpow_mul_exp_neg_rpow hp, add_assoc, one_add_one_eq_two]
    · ring
    · linarith

theorem Complex.integral_exp_neg_rpow :
    ∫ x : ℂ, Real.exp (- ‖x‖ ^ p) = Real.pi * Real.Gamma (2 / p + 1) := by
  convert (integral_rpow_mul_exp_neg_rpow hp (by linarith : (-2:ℝ) < 0)) using 1
  · simp_rw [norm_eq_abs, Real.rpow_zero, one_mul]
  · rw [zero_add, Real.Gamma_add_one (div_ne_zero two_ne_zero (ne_of_gt hp))]
    ring

end p_pos

-- TODO: generalize to other measures?

theorem MeasureTheory.lintegral_fin_prod_eq_pow {E : Type*} {n : ℕ} (hn : 1 ≤ n) {f : E → ENNReal}
    [MeasureSpace E] [SigmaFinite (volume : Measure E)] (hf : Measurable f) :
    ∫⁻ x : Fin n → E, ∏ i, f (x i) = (∫⁻ x, f x) ^ n := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [← (volume_preserving_funUnique (Fin 1) E).lintegral_comp hf]
      simp [Nat.zero_eq, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
        MeasurableEquiv.funUnique_apply, pow_one]
  | succ n _ n_ih =>
      have h_mes : ∀ n, Measurable (fun (y : Fin n → E) => ∏ i : Fin n, f (y i)) :=
        fun _ => Measurable.finset_prod Finset.univ (fun i _ => hf.comp (measurable_pi_apply i))
      calc
        _ = ∫⁻ x : E × (Fin n → E), (f x.1) * ∏ i : Fin n, f (x.2 i) := by
          rw [volume_pi, ← ((measurePreserving_piFinSuccAboveEquiv
            (fun _ => (volume : Measure E)) 0).symm).lintegral_comp (h_mes _)]
          simp_rw [MeasurableEquiv.piFinSuccAboveEquiv_symm_apply, Fin.insertNth_zero',
            Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
          rfl
        _ = (∫⁻ x, f x) * (∫⁻ x, f x) ^ n := by
          rw [volume_eq_prod, lintegral_prod, ← lintegral_mul_const _ hf]
          simp_rw [lintegral_const_mul _ (h_mes _), n_ih]
          refine (hf.aemeasurable.comp_measurable measurable_fst).mul ?_
          exact Measurable.aemeasurable ((h_mes _).comp (f := fun x : _ × _ => x.2) measurable_snd)
        _ = (∫⁻ x, f x) ^ n.succ := by rw [← pow_succ]

theorem MeasureTheory.lintegral_prod_eq_pow {E : Type*} (ι : Type*) [Fintype ι] [Nonempty ι]
    {f : E → ENNReal} [MeasureSpace E] [SigmaFinite (volume : Measure E)] (hf : Measurable f) :
    ∫⁻ x : ι → E, ∏ i, f (x i) = (∫⁻ x, f x) ^ (card ι) := by
  let s := MeasurableEquiv.piCongrLeft (fun _ => E) (equivFin ι)
  have : MeasurePreserving s := by exact
    volume_measurePreserving_piCongrLeft (fun _ ↦ E) (equivFin ι)
  have := MeasurePreserving.lintegral_comp this.symm (f := fun x => ∏ i, f (x i)) ?_
  rw [← this]
  have t1 := fun x : Fin (card ι) → E => Fintype.prod_equiv (equivFin ι)
    (fun i => f ((s.symm x) i)) (fun i => f (x i)) ?_
  simp_rw [t1]
  have : card ι ≠0  := by exact card_ne_zero
  have : 1 ≤ card ι := by exact Nat.one_le_iff_ne_zero.mpr this
  have := MeasureTheory.lintegral_fin_prod_eq_pow this hf
  rw [this]
  intro x
  rfl
  exact Measurable.finset_prod _ fun _ _ =>  hf.comp (measurable_pi_apply _)

theorem MeasureTheory.integral_prod_eq_pow {E : Type*} (ι : Type*) [Fintype ι] [Nonempty ι]
    {f : E → ℝ} [MeasureSpace E] [SigmaFinite (volume : Measure E)] :
    ∫ x : ι → E, ∏ i, f (x i) = (∫ x, f x) ^ (card ι) := by
  sorry

variable (ι : Type*) [Fintype ι] [Nontrivial ι]

open FiniteDimensional

theorem MeasureTheory.measure_unitBall_eq_integral_div_gamma {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] [Nontrivial E] (μ : Measure E) [IsAddHaarMeasure μ] (hp : 0 < p) :
    (μ (Metric.ball 0 1)).toReal =
    (∫ (x : E), Real.exp (- ‖x‖ ^ p) ∂μ) / Real.Gamma (finrank ℝ E / p + 1) := by
  have h_pos : 0 < (finrank ℝ E) / p := div_pos (by simp only [Nat.cast_pos, finrank_pos]) hp
  rw [integral_fun_norm_addHaar μ (fun x => Real.exp (- x ^ p)), eq_div_iff]
  · simp_rw [← Real.rpow_nat_cast _ (finrank ℝ E - 1), smul_eq_mul, Nat.cast_sub finrank_pos,
      Nat.cast_one]
    rw [integral_rpow_mul_exp_neg_rpow hp, sub_add_cancel, Real.Gamma_add_one (ne_of_gt h_pos)]
    · ring
    · simp only [neg_lt_sub_iff_lt_add, lt_add_iff_pos_right, Nat.cast_pos, finrank_pos]
  · exact ne_of_gt (Real.Gamma_pos_of_pos (lt_add_of_pos_of_lt h_pos  Real.zero_lt_one))

end tools

section PiLp

-- TODO. Do the WithLp version instead, generalize to mixed E

open ENNReal Fintype

variable (E ι : Type*) [Fintype ι] (p : ENNReal)

instance [MeasurableSpace E] : MeasurableSpace (PiLp p fun _ : ι => E) :=
  MeasurableSpace.map (WithLp.equiv p _) MeasurableSpace.pi

noncomputable instance [MeasureSpace E] :
  MeasureSpace (PiLp p fun _ : ι => E) := MeasureSpace.pi

noncomputable instance [Fact (1 ≤ p)] : PseudoEMetricSpace (PiLp p fun _ : ι => ℝ) :=
  PiLp.pseudoEmetricAux _ _

local instance [TopologicalSpace E] : TopologicalSpace (PiLp p fun _ : ι => E) :=
  Pi.topologicalSpace

instance [MeasurableSpace E] [TopologicalSpace E]
    [TopologicalSpace.SecondCountableTopology E] [BorelSpace E] :
    BorelSpace (PiLp p fun _ : ι => E) :=
  Pi.borelSpace

local instance [AddGroup E] : AddGroup (PiLp p fun _ : ι => E) := Pi.addGroup

instance [MeasureSpace E] [TopologicalSpace E] [AddGroup E]
    [IsAddHaarMeasure (volume : Measure E)] [SigmaFinite (volume : Measure E)] [MeasurableAdd E] :
    IsAddHaarMeasure (volume : Measure (PiLp p fun _ : ι => E)) :=
  MeasureTheory.Measure.instIsAddHaarMeasureForAllAddGroupTopologicalSpaceToMeasurableSpacePiVolume

theorem WithLp.finrank [Ring E] [StrongRankCondition E] :
    FiniteDimensional.finrank E (PiLp p fun _ : ι ↦ E) = card ι := FiniteDimensional.finrank_pi _

end PiLp

open Fintype ENNReal

variable (ι : Type*) [Fintype ι] {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]

example [Nonempty ι] :
    (volume (Metric.ball (0 : (PiLp (ENNReal.ofReal p) fun _ : ι => ℝ)) 1)).toReal =
      (2 * Real.Gamma (1 / p + 1)) ^ card ι /
        Real.Gamma (card ι / p + 1) := by
  convert measure_unitBall_eq_integral_div_gamma
    (volume : Measure (PiLp (ENNReal.ofReal p) fun _ : ι => ℝ))
    (by sorry : (0:ℝ) < p) using 3
  · simp_rw [PiLp.norm_eq_sum sorry, Real.norm_eq_abs, ← Real.rpow_mul sorry,
      toReal_ofReal sorry, div_mul_cancel _ sorry, Real.rpow_one, ← Finset.sum_neg_distrib, Real.exp_sum]
    erw [integral_prod_eq_pow ι (f := fun x => Real.exp (- |x| ^ p))]
    rw [integral_comp_abs (f := fun x => Real.exp (- x ^ p))]
    · rw [integral_exp_neg_rpow (by sorry : (0:ℝ) < p)]
      rw [Real.Gamma_add_one, nsmul_eq_mul, Nat.cast_ofNat]
      sorry
    · convert integrable_rpow_mul_exp_neg_rpow neg_one_lt_zero hp using 1
      simp_rw [Real.rpow_zero, one_mul]
  · rw [WithLp.finrank]

section generic

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

open FiniteDimensional

theorem MeasureTheory.generic_unitBall_eq_integral_exp_neg_rpow_div_gamma {E : Type*}
    [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] [mE : MeasurableSpace E]
    [tE : TopologicalSpace E] [TopologicalAddGroup E] [BorelSpace E] [T2Space E]
    [Nontrivial E] [ContinuousSMul ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    {g : E → ℝ} (hg0 : g 0 = 0) (hgn : ∀ x, g (- x) = g x) (hgt : ∀ x y, g (x + y) ≤ g x + g y)
    (hgs : ∀ {x}, g x = 0 → x = 0) (hns :  ∀ r x, g (r • x) ≤ |r| * (g x)) :
    (μ {x : E | g x < 1}).toReal =
      (∫ (x : E), Real.exp (- (g x)) ∂μ) / Real.Gamma (finrank ℝ E + 1) := by
  -- We copy `E` to a new type `F` on which we will put the norm defined by `g`
  letI F : Type _ := E
  letI : NormedAddCommGroup F :=
  { norm := g
    dist := fun x y => g (x - y)
    dist_self := by simp only [_root_.sub_self, hg0, forall_const]
    dist_comm := fun _ _ => by dsimp [dist]; rw [← hgn, neg_sub]
    dist_triangle := by
      intro x y z
      dsimp only
      convert hgt (x - y) (y - z) using 2
      abel
    edist := fun x y => ENNReal.ofReal (g (x - y))
    edist_dist := fun _ _ => rfl
    eq_of_dist_eq_zero := by convert fun _ _ h => eq_of_sub_eq_zero (hgs h) }
  letI : NormedSpace ℝ F :=
  { norm_smul_le := fun _ _ =>  hns _ _ }
  -- We put the new topology on F
  letI : TopologicalSpace F := UniformSpace.toTopologicalSpace
  letI : MeasurableSpace F := borel F
  have : BorelSpace F := { measurable_eq := rfl }
  -- The map between `E` and `F` as a continuous linear equivalence
  let φ := @LinearEquiv.toContinuousLinearEquiv ℝ _ E _ _ tE _ _ F _ _ _ _ _ _ _ _ _
    (LinearEquiv.refl ℝ E : E ≃ₗ[ℝ] F)
  -- The measure `ν` is the measure on `F` defined by `μ`
  -- Since we have two different topologies, it is necessary to specify them everywhere
  let ν : Measure F := @Measure.map E F _ mE φ μ
  have : IsAddHaarMeasure ν :=
    @ContinuousLinearEquiv.isAddHaarMeasure_map E F ℝ ℝ _ _ _ _ _ _ tE _ _ _ _ _ _ _ _ mE _ _ _
      φ μ _
  convert (measure_unitBall_eq_integral_div_gamma ν zero_lt_one) using 2
  · rw [@Measure.map_apply E F mE _ μ φ _ _ measurableSet_ball]
    · congr
      ext
      rw [Set.mem_setOf_eq, Set.mem_preimage, mem_ball_zero_iff]
      rfl
    · refine @Continuous.measurable E F tE mE _ _ _ _ φ ?_
      exact @ContinuousLinearEquiv.continuous ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
  · simp_rw [Real.rpow_one]
    let ζ := @ContinuousLinearEquiv.toHomeomorph ℝ ℝ _ _ _ _ _ _ E tE _ F _ _ _ _ φ
    let ψ := @Homeomorph.toMeasurableEquiv E F tE mE _ _ _ _ ζ
    have : @MeasurePreserving E F mE _ ψ μ ν := by
      refine @Measurable.measurePreserving E F mE _ ?_ ?_ _
      · exact @MeasurableEquiv.measurable E F mE _ ψ
    erw [← this.integral_comp]
    rfl
    exact @MeasurableEquiv.measurableEmbedding E F mE _ ψ
  · rw [div_one]

example : (volume {x : ℂ | ‖x‖ < 1}).toReal = Real.pi := by
  rw [generic_unitBall_eq_integral_exp_neg_rpow_div_gamma (volume : Measure ℂ)
    norm_zero norm_neg norm_add_le norm_eq_zero.mp]
  · have := Complex.integral_exp_neg_rpow zero_lt_one
    simp_rw [Real.rpow_one] at this
    rw [this, Complex.finrank_real_complex, div_one, Nat.cast_ofNat, mul_div_cancel]
    exact (ne_of_gt (Real.Gamma_pos_of_pos (by linarith)))
  · intro _ _
    simp only [Complex.real_smul, norm_mul, Complex.norm_eq_abs, Complex.abs_ofReal, le_refl]
