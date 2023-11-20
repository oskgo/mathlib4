/-
Copyright (c) 2023 Adrian Wüthrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Wüthrich
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Rank
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Finrank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
# Laplacian Matrix

In this file we introduce `foo` and `bar`,
two main concepts in the theory of xyzzyology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.
- `bar_of_foo`: a construction of a `bar`, given a `foo`.
- `bar_eq`    : the main classification theorem of `bar`s.

-/


open BigOperators Finset Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def SimpleGraph.degMatrix (R : Type*) [Ring R] : Matrix V V R := Matrix.diagonal (G.degree ·)

def SimpleGraph.lapMatrix (R : Type*) [Ring R] : Matrix V V R := G.degMatrix R - G.adjMatrix R

@[simp]
theorem transpose_lapMatrix (R : Type*) [Ring R] : (G.lapMatrix R)ᵀ = G.lapMatrix R := by
  unfold lapMatrix degMatrix
  rw [transpose_sub, diagonal_transpose, transpose_adjMatrix]

@[simp]
theorem isSymm_lapMatrix (R : Type*) [Ring R] : (G.lapMatrix R).IsSymm :=
  transpose_lapMatrix G R

theorem lapMatrix_mulVec_const_eq_zero : mulVec (G.lapMatrix ℤ) (Function.const V 1) = 0 := by
  unfold lapMatrix
  rw [sub_mulVec]
  ext; simp;
  unfold mulVec dotProduct
  simp only [Pi.one_apply, mul_one]
  unfold degMatrix
  unfold diagonal
  simp only [of_apply, sum_ite_eq, mem_univ, ite_true, sub_self]

lemma vec_adjMatrix_vec (x : V → ℝ) :
    x ⬝ᵥ mulVec (G.adjMatrix ℝ) x = ∑ i : V, ∑ j : V, if G.Adj i j then x i * x j else 0 := by
  unfold dotProduct mulVec dotProduct
  simp [mul_sum]

lemma vec_degMatrix_vec (x : V → ℝ) :
    x ⬝ᵥ mulVec (G.degMatrix ℝ) x = ∑ i : V, G.degree i * x i * x i := by
  unfold dotProduct mulVec degMatrix diagonal dotProduct
  simp only [of_apply, mul_comm, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]

lemma sum_adj_eq_degree (i : V) : (G.degree i : ℝ) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  have h : (∑ j : V, if G.Adj i j then 1 else 0) = (G.adjMatrix ℝ).mulVec (Function.const V 1) i
  · unfold mulVec dotProduct
    simp only [sum_boole, mem_univ, forall_true_left, adjMatrix_apply,
               Function.const_apply, mul_one]
  rw [h]
  simp [degree]

lemma ite_sub_distr {α : Type u_1} [NonAssocRing α] (P : Prop) [Decidable P] (a b : α) :
    ((if P then a else 0) - if P then b else 0) = if P then a - b else 0 := by
  split
  · rfl
  · rw [sub_self]

lemma ite_add_distr {α : Type u_1} [NonAssocRing α](P : Prop) [Decidable P] (a b : α) :
    ((if P then a else 0) + if P then b else 0) = if P then a + b else 0 := by
  split
  · rfl
  · rw [add_zero]

theorem vec_lapMatrix_vec (x : V → ℝ) : toLinearMap₂' (G.lapMatrix ℝ) x x =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j)^2 else 0) / 2 := by
  rw [toLinearMap₂'_apply']
  unfold lapMatrix
  rw [sub_mulVec]
  simp only [dotProduct_sub]
  rw [vec_degMatrix_vec, vec_adjMatrix_vec, ← sum_sub_distrib]
  simp only [sum_adj_eq_degree, sum_mul, ← sum_sub_distrib, ite_mul, one_mul,
             zero_mul, ite_sub_distr]
  rw [←half_add_self (∑ x_1 : V, ∑ x_2 : V, _)]
  have h : (∑ i : V, ∑ j : V, if Adj G i j then x i * x i - x i * x j else 0) =
           (∑ i : V, ∑ j : V, if Adj G i j then x j * x j - x j * x i else 0)
  · have h' (i j : V) : (if Adj G i j then x j * x j - x j * x i else 0) =
                        (if Adj G j i then x j * x j - x j * x i else 0) := by simp [adj_comm]
    conv => rhs; arg 2; intro i; arg 2; intro j; rw [h']
    rw [Finset.sum_comm]
  conv => lhs; arg 1; arg 2; rw [h]
  simp [← sum_add_distrib]
  conv => lhs; arg 1; arg 2; intro i; arg 2; intro j; rw [ite_add_distr]
  field_simp
  rw [sum_congr]
  rfl
  intros i _
  rw [sum_congr]
  rfl
  intros j _
  split
  rw [pow_two]
  ring
  rfl

theorem isPosSemidef_lapMatrix : (G.lapMatrix ℝ).PosSemidef := by
  unfold PosSemidef
  constructor
  · unfold IsHermitian; rw [conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · intro x
    rw [star_trivial, ← toLinearMap₂'_apply', vec_lapMatrix_vec, sum_div]
    apply sum_nonneg'
    intro i
    rw [sum_div]
    apply sum_nonneg'
    intro j
    split_ifs
    · apply div_nonneg_iff.mpr
      left
      constructor
      · simp only [Real.rpow_two, sq_nonneg]
      · exact zero_le_two
    · rw [zero_div]

noncomputable def sqrt_diag_matrix (A : Matrix V V ℝ) : Matrix V V ℝ :=
    Matrix.diagonal (λ i ↦ Real.sqrt (Matrix.diag A i))

lemma sqrt_diag_matrix_square (A : Matrix V V ℝ) (h : IsDiag A) (h' : ∀ i : V, 0 ≤ A i i) :
    (sqrt_diag_matrix A).transpose * sqrt_diag_matrix A = A := by
  ext i j
  simp only [sqrt_diag_matrix, diag_apply, diagonal_transpose, mul_apply, ne_eq, diagonal_apply,
    mul_ite, ite_mul, zero_mul, mul_zero, sum_ite_eq', mem_univ, ite_true]
  split_ifs with hij
  · rw [hij, Real.mul_self_sqrt]
    exact h' j
  · rw [← h]
    exact hij

theorem spd_matrix_zero (A : Matrix V V ℝ) (h_psd : PosSemidef A) (x : V → ℝ) :
    Matrix.toLinearMap₂' A x x = 0 ↔ Matrix.toLinearMap₂' A x = 0 := by
  apply Iff.intro
  · simp only [LinearMap.ext_iff, toLinearMap₂'_apply']
    conv => rhs; intro y; rw [← h_psd.1, conjTranspose_eq_transpose_of_trivial,
                              mulVec_transpose, dotProduct_comm, ←dotProduct_mulVec];
    simp only [Matrix.IsHermitian.spectral_theorem' h_psd.1, IsROrC.ofReal_real_eq_id,
               Function.comp.left_id]
    rw [← sqrt_diag_matrix_square (diagonal (IsHermitian.eigenvalues h_psd.1)),
        ← Matrix.IsHermitian.conjTranspose_eigenvectorMatrix h_psd.1,
        conjTranspose_eq_transpose_of_trivial, mul_assoc, mul_assoc, ←mul_assoc,
        ← Matrix.mulVec_mulVec]
    · intro h0 y
      rw [dotProduct_mulVec, ← mulVec_transpose] at h0
      simp only [transpose_mul, transpose_transpose, dotProduct_self_eq_zero] at h0
      rw [h0]
      simp only [mulVec_zero, dotProduct_zero, LinearMap.zero_apply]
    · simp only [isDiag_diagonal]
    · intro i
      rw [diagonal_apply_eq]
      apply PosSemidef.eigenvalues_nonneg
      exact h_psd
  · intro h0; rw [h0, LinearMap.zero_apply]

lemma ker_adj_eq2 (x : V → ℝ) :
    Matrix.toLinearMap₂' (G.lapMatrix ℝ) x x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  apply Iff.intro
  · intro h i j
    by_contra hn
    have hc : toLinearMap₂' (G.lapMatrix ℝ) x x > 0
    · rw [vec_lapMatrix_vec, sum_div]
      apply sum_pos'
      · simp [sum_div]
        intro i
        apply sum_nonneg'
        intro j
        split_ifs
        · apply div_nonneg_iff.mpr
          left
          constructor
          · exact sq_nonneg (x i - x j)
          · exact zero_le_two
        · rw [zero_div]
      · simp only [mem_univ, true_and]
        use i
        rw [sum_div]
        apply sum_pos'
        · simp only [mem_univ, forall_true_left]
          intro j
          apply div_nonneg_iff.mpr
          left
          constructor
          · split
            · simp only [Real.rpow_two, sq_nonneg]
            · rfl
          · exact zero_le_two
        · simp only [mem_univ, true_and]
          use j
          push_neg at hn
          simp only [hn, ite_true, gt_iff_lt, sub_pos]
          apply div_pos_iff.mpr
          left
          constructor
          · apply sq_pos_of_ne_zero
            rw [sub_ne_zero]
            exact hn.2
          · exact zero_lt_two
    clear hn i j
    absurd hc
    simp only [h, lt_self_iff_false, not_false_eq_true]
  · intro h
    rw [vec_lapMatrix_vec, sum_div]
    apply sum_eq_zero
    intro i
    simp only [mem_univ, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false, forall_true_left]
    apply sum_eq_zero
    intro j
    specialize h i j
    simp only [mem_univ, Real.rpow_two, ite_eq_right_iff, zero_lt_two, pow_eq_zero_iff, sub_eq_zero,
               forall_true_left]
    exact h

theorem ker_adj_eq (x : V → ℝ) :
    Matrix.toLinearMap₂' (G.lapMatrix ℝ) x = 0 ↔ ∀ i j : V, G.Adj i j → x i = x j := by
  rw [← spd_matrix_zero (G.lapMatrix ℝ) (isPosSemidef_lapMatrix G), ker_adj_eq2]

lemma ker_reachable_eq2 (x : V → ℝ) : Matrix.toLinearMap₂' (G.lapMatrix ℝ) x x = 0 ↔
    ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [ker_adj_eq2]
  apply Iff.intro
  · intro h i j
    unfold Reachable
    simp
    intro w
    induction' w with w i j _ hA _ h'
    · rfl
    · rw [← h']
      specialize h i j
      rw [h]
      exact hA
  · intro h i j hA
    specialize h i j
    have hR : Reachable G i j
    · simp only [Adj.reachable hA]
    simp [hR] at h
    exact h

theorem ker_reachable_eq (x : V → ℝ) : Matrix.toLinearMap₂' (G.lapMatrix ℝ) x = 0 ↔
    ∀ i j : V, G.Reachable i j → x i = x j := by
  rw [← spd_matrix_zero (G.lapMatrix ℝ) (isPosSemidef_lapMatrix G), ker_reachable_eq2]

variable [DecidableEq G.ConnectedComponent]

def lapMatrix_ker_basis_aux (c : G.ConnectedComponent) :
    LinearMap.ker (Matrix.toLinearMap₂' (G.lapMatrix ℝ)) :=
  ⟨fun i ↦ if G.connectedComponentMk i = c then 1 else 0, by
  rw [LinearMap.mem_ker, ker_reachable_eq]
  intro i j h
  split_ifs with h₁ h₂ h₃
  · rfl
  · simp only [one_ne_zero]
    rw [← ConnectedComponent.eq] at h
    absurd h₂
    rw [← h₁, h]
  · simp only [zero_ne_one]
    rw [← ConnectedComponent.eq] at h
    absurd h₁
    rw [← h₃, h]
  · rfl
  ⟩

lemma lapMatrix_ker_basis_aux_linearIndependent :
    LinearIndependent ℝ (lapMatrix_ker_basis_aux G) := by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c : ConnectedComponent G,
      g c • lapMatrix_ker_basis_aux G c = fun i ↦ g (connectedComponentMk G i)
  · unfold lapMatrix_ker_basis_aux
    simp
    conv => lhs; simp;
    have hs : ∀ c,  g c • (fun i ↦ if connectedComponentMk G i = c then (1 : ℝ) else 0) =
                           fun i ↦ if connectedComponentMk G i = c then g c else 0
    · intro c
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp only [hs]
    ext i
    simp only [Finset.sum_apply, sum_ite_eq, mem_univ, ite_true]
  rw [h] at h0
  intro c
  have he : ∃ i : V, G.connectedComponentMk i = c
  · exact Quot.exists_rep c
  obtain ⟨i, h'⟩ := he
  rw [← h']
  apply congrFun h0

lemma lapMatrix_ker_basis_aux_spanning :
    ⊤ ≤ Submodule.span ℝ (Set.range (lapMatrix_ker_basis_aux G)) := by
  intro x _
  rw [mem_span_range_iff_exists_fun]
  have h : ∀ (i j : V) (w : SimpleGraph.Walk G i j), SimpleGraph.Walk.IsPath w → x.val i = x.val j
  · intro i j w _
    suffices hr : Reachable G i j
    · have h' : ∀ (i j : V), Reachable G i j → x.val i = x.val j
      · rw [← ker_reachable_eq G x, LinearMap.map_coe_ker]
      · specialize h' i j
        apply h'
        exact hr
    simp only [Walk.reachable w]
  use ConnectedComponent.lift x.val h
  ext j
  simp only [AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid, SetLike.val_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold lapMatrix_ker_basis_aux
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ConnectedComponent.lift_mk, ite_true]

noncomputable def lapMatrix_ker_basis :=
    Basis.mk (lapMatrix_ker_basis_aux_linearIndependent G) (lapMatrix_ker_basis_aux_spanning G)

theorem rank_ker_lapMatrix_eq_card_ConnectedComponent : Fintype.card G.ConnectedComponent =
    FiniteDimensional.finrank ℝ (LinearMap.ker (Matrix.toLinearMap₂' (G.lapMatrix ℝ))) := by
  rw [FiniteDimensional.finrank_eq_card_basis (lapMatrix_ker_basis G)]
