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
import Mathlib.Combinatorics.SetFamily.ExchangeAxiom

/-- Language version of greedoid. -/
structure GreedoidLanguage (α : Type _) [Fintype α] where
  /-- `language` is a finite sequence of simple words. -/
  language : Language α
  /-- Every words of the `language` are simple, i.e., no words contains duplicates. -/
  nodup : ∀ {l}, l ∈ language → l.Nodup
  /-- `language` contains an empty word. -/
  containsEmpty : [] ∈ language
  /-- For every word `w = w₂ ++ w₁ ∈ language`, `w₁ ∈ language` also holds. -/
  containsPrefix : ∀ {l₁ l₂ : List α}, l₂ ++ l₁ ∈ language → l₁ ∈ language
  /-- Exchange Axiom -/
  exchangeAxiom : {l₁ : List α} → l₁ ∈ language → {l₂ : List α} → l₂ ∈ language →
    l₁.length > l₂.length → ∃ x ∈ l₁, x :: l₂ ∈ language

-- GreedoidLanguage is not decidable, as long as it uses `Language`.

namespace GreedoidLanguage

variable {α : Type _}

/-- List of axioms in `GreedoidLanguage` -/
def greedoidLanguageAxiom (Lang : Language α) :=
  (∀ {l}, l ∈ Lang → l.Nodup) ∧
  ([] ∈ Lang) ∧
  (∀ {l₁ l₂ : List α}, l₂ ++ l₁ ∈ Lang → l₁ ∈ Lang) ∧
  ({l₁ : List α} → l₁ ∈ Lang → {l₂ : List α} → l₂ ∈ Lang →
    l₁.length > l₂.length → ∃ x ∈ l₁, x :: l₂ ∈ Lang)

protected theorem eq_of_veq [Fintype α] :
    ∀ {L₁ L₂ : GreedoidLanguage α}, L₁.language = L₂.language → L₁ = L₂
  | ⟨l₁, _, _, _, _⟩, ⟨l₂, _, _, _, _⟩, h => by cases h; rfl

theorem greedoidLanguageAxiom_greedoidLangauge [Fintype α] {L : GreedoidLanguage α} :
    greedoidLanguageAxiom L.language :=
  ⟨L.nodup, L.containsEmpty, L.containsPrefix, L.exchangeAxiom⟩

instance [DecidableEq α] [Fintype α] {L : GreedoidLanguage α} :
    Language.Hereditary L.language where
  nodup := L.nodup
  containsEmpty := L.containsEmpty
  containsPrefix := L.containsPrefix

noncomputable instance [DecidableEq α] [Fintype α] {L : GreedoidLanguage α} :
    Fintype L.language.Elem :=
  Language.fintypeLanguage

end GreedoidLanguage

/-- Set System version of greedoid. -/
structure GreedoidSystem (α : Type _) [Fintype α] [DecidableEq α] where
  /-- `feasibleSet` contains sets which are feasible. -/
  feasibleSet : Finset (Finset α)
  /-- `feasibleSet` contains an empty set. -/
  containsEmpty : ∅ ∈ feasibleSet
  /-- `feasible_set` is accessible. -/
  accessible : ∀ {s}, s ∈ feasibleSet → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ feasibleSet
  /-- Exchange Axiom -/
  exchangeAxiom : exchangeAxiom feasibleSet

namespace GreedoidSystem

variable {α : Type _} [DecidableEq α]

/-- List of axioms in `GreedoidSystem` -/
def greedoidSystemAxiom (Sys : Finset (Finset α)) :=
  ∅ ∈ Sys ∧ (∀ {s}, s ∈ Sys → s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys) ∧ _root_.exchangeAxiom Sys

instance : DecidablePred (@greedoidSystemAxiom α _) := fun Sys =>
  if h₁ : ∅ ∈ Sys
  then if h₂ : ∀ s ∈ Sys, s ≠ ∅ → ∃ x ∈ s, s \ {x} ∈ Sys
    then if h₃ : _root_.exchangeAxiom Sys
      then isTrue (by simp_all [greedoidSystemAxiom])
      else isFalse (by simp [greedoidSystemAxiom, h₃])
    else isFalse (by simp [greedoidSystemAxiom, h₂])
  else isFalse (by simp [greedoidSystemAxiom, h₁])

protected theorem eq_of_veq [Fintype α] :
    ∀ {S₁ S₂ : GreedoidSystem α}, S₁.feasibleSet = S₂.feasibleSet → S₁ = S₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h => by cases h; rfl

instance [Fintype α] : DecidableEq (GreedoidSystem α) :=
  fun S₁ S₂ =>
    if h : S₁.feasibleSet = S₂.feasibleSet
    then isTrue (GreedoidSystem.eq_of_veq h)
    else isFalse (fun h' => h (by simp only [h']))

theorem greedoidSystemAxiom_greedoidSystem [Fintype α] {S : GreedoidSystem α} :
    greedoidSystemAxiom S.feasibleSet :=
  ⟨S.containsEmpty, S.accessible, S.exchangeAxiom⟩

instance [Fintype α] : Fintype (GreedoidSystem α) where
  elems := ((@Finset.univ α _).powerset.powerset.filter greedoidSystemAxiom).attach.map
    ⟨fun Sys => ⟨Sys.val, by
        let ⟨val, prop⟩ := Sys; simp only; simp at prop; exact prop.1, fun h₁ h₂ => by
        let ⟨val, prop⟩ := Sys; simp only; simp at prop h₁; exact prop.2.1 h₁ h₂,
        fun {_} a {_} b c => by
        let ⟨val, prop⟩ := Sys; simp only; simp at prop a b; exact prop.2.2 a b c⟩,
      fun S₁ S₂ hS => by simp only [GreedoidSystem.mk.injEq] at hS; exact Subtype.ext hS⟩
  complete S := by simp; exists S.feasibleSet; simp only [greedoidSystemAxiom_greedoidSystem]

instance [Fintype α] {S : GreedoidSystem α} :
    Accessible S.feasibleSet where
  containsEmpty := S.containsEmpty
  accessible := S.accessible

end GreedoidSystem

namespace GreedoidLanguage

variable {α : Type _} [DecidableEq α] [Fintype α]

open Nat List Finset Language GreedoidSystem

/-- Converts `GreedoidLanguage α` to `Finset (Finset α)`. -/
noncomputable def fromLanguageToSystem' (L : GreedoidLanguage α) :=
  L.language.toAccessibleSystem

instance AccessibleLanguageToSystem' (L : GreedoidLanguage α) :
    Accessible L.fromLanguageToSystem' where
  containsEmpty := Language.toAccessibleSystem_containsEmpty
  accessible := Language.toAccessibleSystem_accessible

theorem greedoidSystemAxiom_fromLanguageToSystem' {L : GreedoidLanguage α} :
    greedoidSystemAxiom L.fromLanguageToSystem' :=
  sorry

end GreedoidLanguage
