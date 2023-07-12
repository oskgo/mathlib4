import Mathlib.Data.List.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.List.Infix
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.List
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Tactic.TFAE
import Mathlib.Tactic.WLOG
import Mathlib.Combinatorics.SetFamily.Accessible
import Mathlib.Combinatorics.SetFamily.Bases
import Mathlib.Combinatorics.SetFamily.Language

/-- The exchange axiom of set family.
    `Sys` satisfies the exchange property if there is some element `x` in `s₁ \ s₂`
    which `s₂ ∪ {x}` is also feasible,
    for any two feasible sets `s₁` and `s₂` of `Sys` with `s₁.card > s₂.card`. -/
def exchangeAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → (hs₁ : s₁ ∈ Sys) →
  {s₂ : Finset α} → (hs₂ : s₂ ∈ Sys) →
  (hs : s₁.card > s₂.card) →
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys

/-- A weak version of exchange axiom of set system version of greedoid -/
def weakExchangeAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s₁ : Finset α} → (hs₁ : s₁ ∈ Sys) →
  {s₂ : Finset α} → (hs₂ : s₂ ∈ Sys) →
  (hs : s₁.card = s₂.card + 1) →
    ∃ x ∈ s₁ \ s₂, s₂ ∪ {x} ∈ Sys

/-- A weaker version of exchange axiom of set system version of greedoid -/
def weakerExchangeAxiom {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) :=
  {s : Finset α} →
  {x : α} → (hx₁ : x ∉ s) → (hx₂ : s ∪ {x} ∈ Sys) →
  {y : α} → (hy₁ : y ∉ s) → (hy₂ : s ∪ {y} ∈ Sys) →
  {z : α} → (hz : z ∉ s) → (hxz₁ : x ≠ z) →
  (hxz₂ : s ∪ {x, z} ∈ Sys) → (hxy : s ∪ {x, y} ∉ Sys) →
    s ∪ {y, z} ∈ Sys

instance {α : Type _} [DecidableEq α] :
    DecidablePred (@exchangeAxiom α _) := fun Sys =>
  if h : ∀ {s₁}, s₁ ∈ Sys → ∀ {s₂}, s₂ ∈ Sys → s₁.card > s₂.card →
    ∃ x, x ∈ s₁ \ s₂ ∧ s₂ ∪ {x} ∈ Sys
  then isTrue (by intro s₁ hs₁ s₂ hs₂ hs; simp at h; simp; exact h hs₁ hs₂ hs)
  else isFalse (by intro h'; apply h; clear h; simp [exchangeAxiom] at h'; simp; apply h')

section ExchangeAxioms

variable {α : Type _} [DecidableEq α] {Sys : Finset (Finset α)}

open Nat List Finset

theorem exchangeAxiom_to_weakExchangeAxiom (hSys : exchangeAxiom Sys) :
    weakExchangeAxiom Sys :=
  fun {_} hs₁ {_} hs₂ hs => hSys hs₁ hs₂ (by simp only [hs, lt_add_iff_pos_right])

theorem weakExchangeAxiom_to_exchangeAxiom [Accessible Sys] (hSys : weakExchangeAxiom Sys) :
    exchangeAxiom Sys := by
  intro s₁ hs₁ s₂ hs₂ hs
  have s₁_nonempty : s₁ ≠ ∅ := by intro h'; simp only [h', card_empty, not_lt_zero'] at hs
  have ⟨s', hs'₁, hs'₂, hs'₃⟩ : ∃ s', s' ∈ Sys ∧ s' ⊆ s₁ ∧ card s' = card s₂ + 1 :=
    accessible_system_smaller_feasible_set hs₁ s₁_nonempty (by simp_arith at hs; exact hs)
  have ⟨x, hx₁, hx₂⟩:= hSys hs'₁ hs₂ hs'₃
  exists x
  simp only [mem_sdiff] at hx₁
  simp only [mem_sdiff, hx₁, hx₂, and_true]
  exact hs'₂ hx₁.1

theorem exchangeAxiom_weakExchangeAxiom_iff [Accessible Sys] :
    exchangeAxiom Sys ↔ weakExchangeAxiom Sys :=
  ⟨exchangeAxiom_to_weakExchangeAxiom, weakExchangeAxiom_to_exchangeAxiom⟩

theorem weakExchangeAxiom_to_weakerExchangeAxiom (hSys : weakExchangeAxiom Sys) :
    weakerExchangeAxiom Sys := by
  intro s x hx₁ _ y hy₁ hy₂ z hz hxz₁ hxz₂ hxy
  let ⟨z', hz₁', hz₂'⟩ := hSys hxz₂ hy₂ (by
    simp [hxz₁, hx₁]
    rw [union_comm, union_comm s {y}, ← insert_eq, ← insert_eq]
    simp [hy₁, hz])
  simp at hz₁'
  let ⟨h₁, h₂⟩ := hz₁'
  have union_lem: ∀ {s : Finset α} {x y : α}, s ∪ {x, y} = s ∪ ({x} ∪ {y}) := by
    intro s x y; simp; rw [union_comm _ ({x} ∪ {y}), union_assoc, union_comm {y} s]; rfl
  apply h₁.elim <;> intro h₁ <;> try (apply h₁.elim <;> intro h₁)
  . exfalso
    simp only [h₁, union_assoc] at hz₂'
    exact hxy ((union_comm {x} {y} ▸ union_lem) ▸ hz₂')
  . exfalso
    exact h₂ (Or.inl h₁)
  . simp only [h₁, union_assoc] at h₂ hz₂'
    exact union_lem ▸ hz₂'

-- TODO: Add `weakerExchangeAxiom_to_weakExchangeAxiom` or `weakerExchangeAxiom_to_exchangeAxiom`

theorem exchangeAxiom_bases_card_iff [Fintype α] :
    exchangeAxiom Sys ↔ (∀ {a : Finset α},
      ∀ {b₁}, b₁ ∈ bases Sys a →
      ∀ {b₂}, b₂ ∈ bases Sys a →
      b₁.card = b₂.card) := by
  constructor <;> intro h
  . intro a b₁ hb₁ b₂ hb₂
    by_contra' h'
    apply (lt_or_gt_of_ne h').elim <;> intro h' <;> simp only [bases, Finset.mem_filter] at hb₁ hb₂
    . let ⟨x, hx₁, hx₂⟩ := h hb₂.1 hb₁.1 h'
      simp only [mem_sdiff] at hx₁
      exact hx₁.2 (hb₁.2.2 (hb₂.2.1 hx₁.1) hx₂)
    . let ⟨x, hx₁, hx₂⟩ := h hb₁.1 hb₂.1 h'
      simp only [mem_sdiff] at hx₁
      exact hx₁.2 (hb₂.2.2 (hb₁.2.1 hx₁.1) hx₂)
  . intro s₁ hs₁ s₂ hs₂ hs
    have ⟨_, hb₁₁, hb₁₂⟩ := exists_basis_containing_feasible_set hs₁ (subset_union_left _ s₂)
    have ⟨b₂, hb₂₁, _⟩ := exists_basis_containing_feasible_set hs₂ (subset_union_right s₁ _)
    have : s₂.card < b₂.card := h hb₂₁ hb₁₁ ▸ lt_of_lt_of_le hs (card_le_of_subset hb₁₂)
    by_contra' h'
    have hs₂_basis : s₂ ∈ bases Sys (s₁ ∪ s₂) := by
      simp only [bases, Finset.mem_union, Finset.mem_filter, hs₂, subset_union_right, true_and]
      intro _ _ h
      by_contra
      exact h' _ (by simp_all) h
    simp only [h hb₂₁ hs₂_basis, lt_self_iff_false] at this

end ExchangeAxioms
