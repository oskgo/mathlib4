/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/

import Mathlib.Algebra.Module.Submodule.Basic

#align_import linear_algebra.basic from "leanprover-community/mathlib"@"9d684a893c52e1d6692a504a118bfccbae04feeb"

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `Module`, `Submodule`, and `LinearMap`, are found in
`Algebra/Module`.

## Main definitions

* Many constructors for (semi)linear maps
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.

See `LinearAlgebra.Span` for the span of a set (as a submodule),
and `LinearAlgebra.Quotient` for quotients by submodules.

## Main theorems

See `LinearAlgebra.Isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`LinearMap.prod`, `LinearMap.coprod`, arithmetic operations like `+`) instead of defining a
function and proving it is linear.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags
linear algebra, vector space, module

-/

-- local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue #2220

open Function

open BigOperators Pointwise

variable {R : Type _} {R₁ : Type _} {R₂ : Type _} {R₃ : Type _} {R₄ : Type _}
variable {S : Type _}
variable {K : Type _} {K₂ : Type _}
variable {M : Type _} {M' : Type _} {M₁ : Type _} {M₂ : Type _} {M₃ : Type _} {M₄ : Type _}
variable {N : Type _} {N₂ : Type _}
variable {ι : Type _}
variable {V : Type _} {V₂ : Type _}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃] [Semiring R₄]
variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [Module R M] [Module R M₁] [Module R₂ M₂] [Module R₃ M₃] [Module R₄ M₄]
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₃₄ : R₃ →+* R₄}
variable {σ₁₃ : R →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R →+* R₄}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
variable [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
variable (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)

@[simp]
theorem map_sum {ι : Type _} {t : Finset ι} {g : ι → M} : f (∑ i in t, g i) = ∑ i in t, f (g i) :=
  f.toAddMonoidHom.map_sum _ _
#align linear_map.map_sum LinearMap.map_sum

theorem comp_assoc (h : M₃ →ₛₗ[σ₃₄] M₄) :
    ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M →ₛₗ[σ₁₄] M₄) = h.comp (g.comp f : M →ₛₗ[σ₁₃] M₃) :=
  rfl
#align linear_map.comp_assoc LinearMap.comp_assoc


/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def domRestrict (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : p →ₛₗ[σ₁₂] M₂ :=
  f.comp p.subtype
#align linear_map.dom_restrict LinearMap.domRestrict

@[simp]
theorem domRestrict_apply (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) (x : p) :
    f.domRestrict p x = f x :=
  rfl
#align linear_map.dom_restrict_apply LinearMap.domRestrict_apply

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀ c, f c ∈ p) : M →ₛₗ[σ₁₂] p := by
  refine' { toFun := fun c => ⟨f c, h c⟩.. } <;> intros <;> apply SetCoe.ext <;> simp
#align linear_map.cod_restrict LinearMap.codRestrict

@[simp]
theorem codRestrict_apply (p : Submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) {h} (x : M) :
    (codRestrict p f h x : M₂) = f x :=
  rfl
#align linear_map.cod_restrict_apply LinearMap.codRestrict_apply

@[simp]
theorem comp_codRestrict (p : Submodule R₃ M₃) (h : ∀ b, g b ∈ p) :
    ((codRestrict p g h).comp f : M →ₛₗ[σ₁₃] p) = codRestrict p (g.comp f) fun _ => h _ :=
  ext fun _ => rfl
#align linear_map.comp_cod_restrict LinearMap.comp_codRestrict

@[simp]
theorem subtype_comp_codRestrict (p : Submodule R₂ M₂) (h : ∀ b, f b ∈ p) :
    p.subtype.comp (codRestrict p f h) = f :=
  ext fun _ => rfl
#align linear_map.subtype_comp_cod_restrict LinearMap.subtype_comp_codRestrict

/-- Restrict domain and codomain of a linear map. -/
def restrict (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    p →ₗ[R] q :=
  (f.domRestrict p).codRestrict q <| SetLike.forall.2 hf
#align linear_map.restrict LinearMap.restrict

@[simp]
theorem restrict_coe_apply (f : M →ₗ[R] M₁) {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : ↑(f.restrict hf x) = f x :=
  rfl
#align linear_map.restrict_coe_apply LinearMap.restrict_coe_apply

theorem restrict_apply {f : M →ₗ[R] M₁} {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) (x : p) : f.restrict hf x = ⟨f x, hf x.1 x.2⟩ :=
  rfl
#align linear_map.restrict_apply LinearMap.restrict_apply

theorem subtype_comp_restrict {f : M →ₗ[R] M₁} {p : Submodule R M} {q : Submodule R M₁}
    (hf : ∀ x ∈ p, f x ∈ q) : q.subtype.comp (f.restrict hf) = f.domRestrict p :=
  rfl
#align linear_map.subtype_comp_restrict LinearMap.subtype_comp_restrict

theorem restrict_eq_codRestrict_domRestrict {f : M →ₗ[R] M₁} {p : Submodule R M}
    {q : Submodule R M₁} (hf : ∀ x ∈ p, f x ∈ q) :
    f.restrict hf = (f.domRestrict p).codRestrict q fun x => hf x.1 x.2 :=
  rfl
#align linear_map.restrict_eq_cod_restrict_dom_restrict LinearMap.restrict_eq_codRestrict_domRestrict

theorem restrict_eq_domRestrict_codRestrict {f : M →ₗ[R] M₁} {p : Submodule R M}
    {q : Submodule R M₁} (hf : ∀ x, f x ∈ q) :
    (f.restrict fun x _ => hf x) = (f.codRestrict q hf).domRestrict p :=
  rfl
#align linear_map.restrict_eq_dom_restrict_cod_restrict LinearMap.restrict_eq_domRestrict_codRestrict

instance uniqueOfLeft [Subsingleton M] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  { inferInstanceAs (Inhabited (M →ₛₗ[σ₁₂] M₂)) with
    uniq := fun f => ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero] }
#align linear_map.unique_of_left LinearMap.uniqueOfLeft

instance uniqueOfRight [Subsingleton M₂] : Unique (M →ₛₗ[σ₁₂] M₂) :=
  coe_injective.unique
#align linear_map.unique_of_right LinearMap.uniqueOfRight

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `AddMonoidHom`. -/
def evalAddMonoidHom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂ where
  toFun f := f a
  map_add' f g := LinearMap.add_apply f g a
  map_zero' := rfl
#align linear_map.eval_add_monoid_hom LinearMap.evalAddMonoidHom

/-- `LinearMap.toAddMonoidHom` promoted to a `AddMonoidHom` -/
def toAddMonoidHom' : (M →ₛₗ[σ₁₂] M₂) →+ M →+ M₂ where
  toFun := toAddMonoidHom
  map_zero' := by ext; rfl
  map_add' := by intros; ext; rfl
#align linear_map.to_add_monoid_hom' LinearMap.toAddMonoidHom'

theorem sum_apply (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) (b : M) :
    (∑ d in t, f d) b = ∑ d in t, f d b :=
  _root_.map_sum ((AddMonoidHom.eval b).comp toAddMonoidHom') f _
#align linear_map.sum_apply LinearMap.sum_apply

section SMulRight

variable [Semiring S] [Module R S] [Module S M] [IsScalarTower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `fun ↦ b, f b • x` is an `R`-linear
map. -/
def smulRight (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M where
  toFun b := f b • x
  map_add' x y := by dsimp only; rw [f.map_add, add_smul]
  map_smul' b y := by dsimp; rw [map_smul, smul_assoc]
#align linear_map.smul_right LinearMap.smulRight

@[simp]
theorem coe_smulRight (f : M₁ →ₗ[R] S) (x : M) : (smulRight f x : M₁ → M) = fun c => f c • x :=
  rfl
#align linear_map.coe_smul_right LinearMap.coe_smulRight

theorem smulRight_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) : smulRight f x c = f c • x :=
  rfl
#align linear_map.smul_right_apply LinearMap.smulRight_apply

end SMulRight

instance [Nontrivial M] : Nontrivial (Module.End R M) := by
  obtain ⟨m, ne⟩ := exists_ne (0 : M)
  exact nontrivial_of_ne 1 0 fun p => ne (LinearMap.congr_fun p m)

@[simp, norm_cast]
theorem coeFn_sum {ι : Type _} (t : Finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) :
    ⇑(∑ i in t, f i ) = ∑ i in t, (f i : M → M₂) :=
  _root_.map_sum
    (show AddMonoidHom (M →ₛₗ[σ₁₂] M₂) (M → M₂)
      from { toFun := FunLike.coe,
             map_zero' := rfl
             map_add' := fun _ _ => rfl }) _ _
#align linear_map.coe_fn_sum LinearMap.coeFn_sum

theorem coe_pow (f : M →ₗ[R] M) (n : ℕ) : ⇑(f ^ n) = f^[n] := hom_coe_pow _ rfl (fun _ _ ↦ rfl) _ _
#align linear_map.coe_pow LinearMap.coe_pow

theorem pow_apply (f : M →ₗ[R] M) (n : ℕ) (m : M) : (f ^ n) m = f^[n] m := congr_fun (coe_pow f n) m
#align linear_map.pow_apply LinearMap.pow_apply

theorem pow_map_zero_of_le {f : Module.End R M} {m : M} {k l : ℕ} (hk : k ≤ l)
    (hm : (f ^ k) m = 0) : (f ^ l) m = 0 := by
  rw [← tsub_add_cancel_of_le hk, pow_add, mul_apply, hm, map_zero]
#align linear_map.pow_map_zero_of_le LinearMap.pow_map_zero_of_le

theorem commute_pow_left_of_commute {f : M →ₛₗ[σ₁₂] M₂} {g : Module.End R M} {g₂ : Module.End R₂ M₂}
    (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂ ^ k).comp f = f.comp (g ^ k) := by
  induction' k with k ih
  · simp only [Nat.zero_eq, pow_zero, one_eq_id, id_comp, comp_id]
  · rw [pow_succ, pow_succ, LinearMap.mul_eq_comp, LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc,
      h, LinearMap.comp_assoc, LinearMap.mul_eq_comp]
#align linear_map.commute_pow_left_of_commute LinearMap.commute_pow_left_of_commute

theorem submodule_pow_eq_zero_of_pow_eq_zero {N : Submodule R M} {g : Module.End R N}
    {G : Module.End R M} (h : G.comp N.subtype = N.subtype.comp g) {k : ℕ} (hG : G ^ k = 0) :
    g ^ k = 0 := by
  ext m
  have hg : N.subtype.comp (g ^ k) m = 0 := by
    rw [← commute_pow_left_of_commute h, hG, zero_comp, zero_apply]
  simpa using hg
#align linear_map.submodule_pow_eq_zero_of_pow_eq_zero LinearMap.submodule_pow_eq_zero_of_pow_eq_zero

@[simp]
theorem id_pow (n : ℕ) : (id : M →ₗ[R] M) ^ n = id :=
  one_pow n
#align linear_map.id_pow LinearMap.id_pow

section

variable {f' : M →ₗ[R] M}

theorem iterate_succ (n : ℕ) : f' ^ (n + 1) = comp (f' ^ n) f' := by rw [pow_succ', mul_eq_comp]
#align linear_map.iterate_succ LinearMap.iterate_succ

theorem iterate_surjective (h : Surjective f') : ∀ n : ℕ, Surjective (f' ^ n)
  | 0 => surjective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_surjective h n).comp h
#align linear_map.iterate_surjective LinearMap.iterate_surjective

theorem iterate_injective (h : Injective f') : ∀ n : ℕ, Injective (f' ^ n)
  | 0 => injective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_injective h n).comp h
#align linear_map.iterate_injective LinearMap.iterate_injective

theorem iterate_bijective (h : Bijective f') : ∀ n : ℕ, Bijective (f' ^ n)
  | 0 => bijective_id
  | n + 1 => by
    rw [iterate_succ]
    exact (iterate_bijective h n).comp h
#align linear_map.iterate_bijective LinearMap.iterate_bijective

theorem injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : Injective (f' ^ n)) :
    Injective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), iterate_succ, coe_comp] at h
  exact h.of_comp
#align linear_map.injective_of_iterate_injective LinearMap.injective_of_iterate_injective

theorem surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : Surjective (f' ^ n)) :
    Surjective f' := by
  rw [← Nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), pow_succ, coe_mul] at h
  exact Surjective.of_comp h
#align linear_map.surjective_of_iterate_surjective LinearMap.surjective_of_iterate_surjective

theorem pow_apply_mem_of_forall_mem {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p) (x : M)
    (hx : x ∈ p) : (f' ^ n) x ∈ p := by
  induction' n with n ih generalizing x
  · simpa
  simpa only [iterate_succ, coe_comp, Function.comp_apply, restrict_apply] using ih _ (h _ hx)
#align linear_map.pow_apply_mem_of_forall_mem LinearMap.pow_apply_mem_of_forall_mem

theorem pow_restrict {p : Submodule R M} (n : ℕ) (h : ∀ x ∈ p, f' x ∈ p)
    (h' := pow_apply_mem_of_forall_mem n h) :
    (f'.restrict h) ^ n = (HPow.hPow f' n).restrict h' := by
  ext x
  have : Semiconj (↑) (f'.restrict h) f' := fun _ ↦ restrict_coe_apply _ _ _
  simp [coe_pow, this.iterate_right _ _]
#align linear_map.pow_restrict LinearMap.pow_restrict

end

-- /-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
-- of the canonical basis. -/
-- theorem pi_apply_eq_sum_univ [Fintype ι] [DecidableEq ι] (f : (ι → R) →ₗ[R] M) (x : ι → R) :
--     f x = ∑ i, x i • f fun j => if i = j then 1 else 0 := by
--   conv_lhs => rw [pi_eq_sum_univ x, f.map_sum]
--   refine Finset.sum_congr rfl (fun _ _ => ?_)
--   rw [map_smul]
-- #align linear_map.pi_apply_eq_sum_univ LinearMap.pi_apply_eq_sum_univ

end AddCommMonoid

section Module

variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₂] [Module R M₃] [Module S M₂] [Module S M₃] [SMulCommClass R S M₂]
  [SMulCommClass R S M₃] (f : M →ₗ[R] M₂)

variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `LinearMap.applyₗ` for a version where `S = R`. -/
@[simps]
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ where
  toFun v :=
    { toFun := fun f => f v
      map_add' := fun f g => f.add_apply g v
      map_smul' := fun x f => f.smul_apply x v }
  map_zero' := LinearMap.ext fun f => f.map_zero
  map_add' _ _ := LinearMap.ext fun f => f.map_add _ _
#align linear_map.applyₗ' LinearMap.applyₗ'

section

variable (R M)

/-- The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
def ringLmapEquivSelf [Module S M] [SMulCommClass R S M] : (R →ₗ[R] M) ≃ₗ[S] M :=
  { applyₗ' S (1 : R) with
    toFun := fun f => f 1
    invFun := smulRight (1 : R →ₗ[R] R)
    left_inv := fun f => by
      ext
      simp only [coe_smulRight, one_apply, smul_eq_mul, ← map_smul f, mul_one]
    right_inv := fun x => by simp }
#align linear_map.ring_lmap_equiv_self LinearMap.ringLmapEquivSelf

end

end Module

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f g : M →ₗ[R] M₂)

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def compRight (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] M →ₗ[R] M₃ where
  toFun := f.comp
  map_add' _ _ := LinearMap.ext fun _ => map_add f _ _
  map_smul' _ _ := LinearMap.ext fun _ => map_smul f _ _
#align linear_map.comp_right LinearMap.compRight

@[simp]
theorem compRight_apply (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂) : compRight f g = f.comp g :=
  rfl
#align linear_map.comp_right_apply LinearMap.compRight_apply

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `LinearMap.applyₗ'` for a version that works with two different semirings.

This is the `LinearMap` version of `toAddMonoidHom.eval`. -/
@[simps]
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
  { applyₗ' R with
    toFun := fun v => { applyₗ' R v with toFun := fun f => f v }
    map_smul' := fun _ _ => LinearMap.ext fun f => map_smul f _ _ }
#align linear_map.applyₗ LinearMap.applyₗ

/-- Alternative version of `domRestrict` as a linear map. -/
def domRestrict' (p : Submodule R M) : (M →ₗ[R] M₂) →ₗ[R] p →ₗ[R] M₂ where
  toFun φ := φ.domRestrict p
  map_add' := by simp [LinearMap.ext_iff]
  map_smul' := by simp [LinearMap.ext_iff]
#align linear_map.dom_restrict' LinearMap.domRestrict'

@[simp]
theorem domRestrict'_apply (f : M →ₗ[R] M₂) (p : Submodule R M) (x : p) :
    domRestrict' p f x = f x :=
  rfl
#align linear_map.dom_restrict'_apply LinearMap.domRestrict'_apply

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M where
  toFun f :=
    { toFun := LinearMap.smulRight f
      map_add' := fun m m' => by
        ext
        apply smul_add
      map_smul' := fun c m => by
        ext
        apply smul_comm }
  map_add' f f' := by
    ext
    apply add_smul
  map_smul' c f := by
    ext
    apply mul_smul
#align linear_map.smul_rightₗ LinearMap.smulRightₗ

@[simp]
theorem smulRightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
    (smulRightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x c = f c • x :=
  rfl
#align linear_map.smul_rightₗ_apply LinearMap.smulRightₗ_apply

end CommSemiring

end LinearMap
