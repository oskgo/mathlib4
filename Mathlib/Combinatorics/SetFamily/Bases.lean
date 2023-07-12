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

/-- Base of a set system is the collection of feasible sets which is maximal. -/
def base {α : Type _} [Fintype α] [DecidableEq α] (Sys : Finset (Finset α)) :=
  Sys.filter (fun s => ∀ {a}, s ∪ {a} ∈ Sys → a ∈ s)

/-- Bases of a set `a` given a set system is
    the collection of feasible sets which is maximal in `a`. -/
def bases {α : Type _} [Fintype α] [DecidableEq α] (Sys : Finset (Finset α)) (s : Finset α) :=
  Sys.filter (fun s' => s' ⊆ s ∧ (∀ {a}, a ∈ s → s' ∪ {a} ∈ Sys → a ∈ s'))

section Bases

variable {α : Type _} [Fintype α] [DecidableEq α]
variable {Sys : Finset (Finset α)}
variable {s b : Finset α} (hb : b ∈ bases Sys s)

open Nat Finset

theorem base_bases_eq : base Sys = bases Sys Finset.univ := by ext s; simp [bases, base]

theorem basis_mem_feasible : b ∈ Sys := by simp only [bases, mem_filter] at hb; exact hb.1

theorem basis_subseteq : b ⊆ s := by simp only [bases, mem_filter] at hb; exact hb.2.1

theorem basis_maximal {a : α} (ha₁ : a ∈ s) (ha₂ : b ∪ {a} ∈ Sys) :
    a ∈ b := by
  simp only [bases, mem_filter] at hb; exact hb.2.2 ha₁ ha₂

theorem exists_basis_containing_feasible_set {s' : Finset α} (hs'₁ : s' ∈ Sys) (hs'₂ : s' ⊆ s) :
    ∃ b ∈ bases Sys s, s' ⊆ b := by
  by_cases h : ∀ x ∈ s, s' ∪ {x} ∈ Sys → x ∈ s'
  . exists s'
    simp only [Subset.refl, and_true, bases, mem_filter, hs'₁, hs'₂, true_and]
    exact fun {a} => h a
  . simp only [not_forall, exists_prop, exists_and_left] at h
    have ⟨x, hx₁, hx₂, _⟩ := h
    have ⟨b, hb₁, hb₂⟩ := exists_basis_containing_feasible_set hx₂ (by
      intro y h
      simp only [mem_union, mem_singleton] at h
      exact h.elim (fun h => hs'₂ h) (fun h => h ▸ hx₁))
    exists b
    apply And.intro hb₁
    intro y hy
    exact hb₂ (mem_union.mpr (Or.inl hy))
termination_by exists_basis_containing_feasible_set => s.card - s'.card
decreasing_by
  simp_wf
  have hx₃ := ‹x ∉ s'›
  exact Nat.sub_lt_sub_left
    (card_lt_card ((ssubset_iff_of_subset hs'₂).mpr ⟨x, hx₁, hx₃⟩))
    (by simp [hx₃])

theorem accessible_bases_nonempty {Sys : Finset (Finset α)} [Accessible Sys] {s : Finset α} :
    Nonempty (bases Sys s) := by
  simp only [nonempty_subtype]
  have ⟨b, _⟩ :=
    exists_basis_containing_feasible_set (@accessible_containsEmpty _ _ Sys _) (empty_subset s)
  exists b; tauto

end Bases
