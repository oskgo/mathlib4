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

end ExchangeAxioms
