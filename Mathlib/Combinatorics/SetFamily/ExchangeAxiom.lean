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

open Nat List Finset

end ExchangeAxioms
