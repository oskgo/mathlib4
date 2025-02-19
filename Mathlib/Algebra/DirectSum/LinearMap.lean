/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Trace

/-!
# Linear maps between direct sums

This file contains results about linear maps which respect direct sum decompositions of their
domain and codomain.

-/

open Set BigOperators DirectSum

variable {ι R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {N : ι → Submodule R M} [DecidableEq ι] (h : IsInternal N)

namespace LinearMap

/-- If a linear map `f : M₁ → M₂` respects direct sum decompositions of `M₁` and `M₂`, then it has a
block diagonal matrix with respect to bases compatible with the direct sum decompositions. -/
lemma toMatrix_directSum_collectedBasis_eq_blockDiagonal' {R M₁ M₂ : Type*} [CommSemiring R]
    [AddCommMonoid M₁] [Module R M₁] {N₁ : ι → Submodule R M₁} (h₁ : IsInternal N₁)
    [AddCommMonoid M₂] [Module R M₂] {N₂ : ι → Submodule R M₂} (h₂ : IsInternal N₂)
    {κ₁ κ₂ : ι → Type*} [∀ i, Fintype (κ₁ i)] [∀ i, Fintype (κ₂ i)] [∀ i, DecidableEq (κ₁ i)]
    [Fintype ι] (b₁ : (i : ι) → Basis (κ₁ i) R (N₁ i)) (b₂ : (i : ι) → Basis (κ₂ i) R (N₂ i))
    {f : M₁ →ₗ[R] M₂} (hf : ∀ i, MapsTo f (N₁ i) (N₂ i)) :
    toMatrix (h₁.collectedBasis b₁) (h₂.collectedBasis b₂) f =
    Matrix.blockDiagonal' fun i ↦ toMatrix (b₁ i) (b₂ i) (f.restrict (hf i)) := by
  ext ⟨i, _⟩ ⟨j, _⟩
  simp only [toMatrix_apply, Matrix.blockDiagonal'_apply]
  rcases eq_or_ne i j with rfl | hij
  · simp [h₂.collectedBasis_repr_of_mem _ (hf _ (Subtype.mem _)), restrict_apply]
  · simp [hij, h₂.collectedBasis_repr_of_mem_ne _ hij.symm (hf _ (Subtype.mem _))]

variable [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)]

lemma trace_eq_sum_trace_restrict [Fintype ι]
    {f : M →ₗ[R] M} (hf : ∀ i, MapsTo f (N i) (N i)) :
    trace R M f = ∑ i, trace R (N i) (f.restrict (hf i)) := by
  let b : (i : ι) → Basis _ R (N i) := fun i ↦ Module.Free.chooseBasis R (N i)
  simp_rw [trace_eq_matrix_trace R (h.collectedBasis b),
    toMatrix_directSum_collectedBasis_eq_blockDiagonal' h h b b hf, Matrix.trace_blockDiagonal',
    ← trace_eq_matrix_trace]

end LinearMap
