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

-- Notes: Should rename `SetSystem` to `SetFamily`?

/-- Accessible set systems are defined as an associated set system of hereditary language;
    here we only pick its properties. -/
class Accessible {α : Type _} [DecidableEq α] (Sys : Finset (Finset α)) where
  /-- Accessible set system contains the empty set. -/
  contains_empty : ∅ ∈ Sys
  /-- For some nonempty feasible set of any accessible set system,
      there is some feasible subset of the set
      whose cardinality is exactly one less than the set. -/
  accessible : ∀ s ∈ Sys, s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys

section Accessible

variable {α : Type _} [DecidableEq α]
variable {Sys : Finset (Finset α)} [Accessible Sys]
variable {s : Finset α} (hs₀ : s ∈ Sys)

open Nat Finset

theorem accessible_contains_empty : ∅ ∈ Sys :=
  ‹Accessible Sys›.contains_empty

theorem accessible_accessible (hs₁ : s ≠ ∅) : ∃ x ∈ s, s \ {x} ∈ Sys :=
  ‹Accessible Sys›.accessible _ hs₀ hs₁

theorem accessible_system_smaller_feasible_set_helper (hs₁ : s ≠ ∅) {n : ℕ} (hn : n ≤ s.card) :
    ∃ s' ∈ Sys, s' ⊆ s ∧ s'.card + n = s.card := by
  induction' n with n ih generalizing s
  . exists s
  . have ⟨s', hs'₁, hs'₂, hs'₃⟩ := ih hs₀ hs₁ (le_trans (by simp_arith) hn)
    let ⟨a, ha₁, ha₂⟩ := ‹Accessible Sys›.accessible _ hs'₁ (by
      intro h'
      simp [h'] at hs'₃
      rw [← hs'₃] at hn
      simp_arith at hn)
    exists s' \ {a}
    simp [ha₂, card_sdiff (fun x hx => by simp at hx; simp [hx, ha₁] : {a} ⊆ s')]
    apply And.intro (Subset.trans (sdiff_subset s' {a}) hs'₂)
    rw [succ_eq_add_one, ← Nat.sub_add_comm, ← add_assoc, Nat.add_sub_cancel, hs'₃]
    have h₁ : s'.card = s.card - n := (Nat.sub_eq_of_eq_add hs'₃.symm).symm
    have h₂ : 1 ≤ s.card - n := le_sub_of_add_le (succ_eq_one_add n ▸ hn)
    simp only [h₁, h₂]

theorem accessible_system_smaller_feasible_set (hs₁ : s ≠ ∅) {n : ℕ} (hn : n ≤ s.card) :
    ∃ s' ∈ Sys, s' ⊆ s ∧ s'.card = n := by
  have ⟨s', hs'₁, hs'₂, hs'₃⟩ := accessible_system_smaller_feasible_set_helper hs₀ hs₁
    (sub_le _ _ : s.card - n ≤ s.card)
  exists s'
  simp_arith [hs'₁, hs'₂]
  have : n ≤ s.card + s'.card := le_trans hn (by simp)
  rw [← Nat.add_sub_assoc hn, add_comm, Nat.sub_eq_iff_eq_add this] at hs'₃
  simp_arith at hs'₃
  exact hs'₃

theorem induction_on_accessible {α : Type _} [DecidableEq α]
  {Sys : Finset (Finset α)} [Accessible Sys]
  {s : Finset α} (hs₀ : s ∈ Sys)
  {p : Finset α → Prop}
  (empty : p ∅)
  (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → s ∈ Sys → s ∪ {a} ∈ Sys → p s → p (s ∪ {a})) :
    p s := by
  by_cases s = ∅ <;> simp only [h, empty]
  have ⟨x, hx₁, hx₂⟩ := ‹Accessible Sys›.accessible _ hs₀ h
  have : p (s \ {x}) := induction_on_accessible hx₂ empty insert
  have : p ((s \ {x}) ∪ {x}):= insert
    (fun h => (mem_sdiff.mp h).2 (mem_singleton.mpr rfl)) hx₂ (by
      rw [sdiff_union_self_eq_union, union_comm, ← insert_eq, insert_eq_of_mem hx₁]
      exact hs₀) this
  rw [sdiff_union_self_eq_union, union_comm, ← insert_eq, insert_eq_of_mem hx₁] at this
  exact this
termination_by induction_on_accessible => s.card
decreasing_by
  simp_wf
  rw [card_sdiff (singleton_subset_iff.mpr hx₁), card_singleton]
  simp only [sub_lt (card_pos.mpr ⟨x, hx₁⟩)]

end Accessible
