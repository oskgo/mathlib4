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

open Nat List Finset Language

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
    Hereditary L.language where
  nodup := L.nodup
  containsEmpty := L.containsEmpty
  containsPrefix := L.containsPrefix

noncomputable instance [DecidableEq α] [Fintype α] {L : GreedoidLanguage α} :
    Fintype L.language.Elem :=
  fintypeLanguage

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

theorem fromLanguageToSystem'_containsEmpty {L : GreedoidLanguage α} :
    ∅ ∈ L.fromLanguageToSystem' :=
  Language.toAccessibleSystem_containsEmpty

theorem fromLanguageToSystem'_accessible {L : GreedoidLanguage α}
  {s : Finset α} (hs₀ : s ∈ L.fromLanguageToSystem') (hs₁ : s ≠ ∅) :
    ∃ x ∈ s, s \ {x} ∈ L.fromLanguageToSystem' :=
  toAccessibleSystem_accessible hs₀ hs₁

instance AccessibleLanguageToSystem' (L : GreedoidLanguage α) :
    Accessible L.fromLanguageToSystem' where
  containsEmpty := fromLanguageToSystem'_containsEmpty
  accessible := fromLanguageToSystem'_accessible

theorem fromLanguageToSystem'_exchangeAxiom {L : GreedoidLanguage α} :
    _root_.exchangeAxiom L.fromLanguageToSystem' := by
  simp only [_root_.exchangeAxiom, fromLanguageToSystem']
  intro s₁ hs₁
  apply induction_on_accessible hs₁ <;> try (intro s₂ hs₂ hs; contradiction)
  intro a s₂ ha₁ _ ha₂ ih s₃ hs₃ hs
  simp_arith [ha₁] at hs
  rw [le_iff_lt_or_eq] at hs
  apply hs.elim <;> intro hs
  . have ⟨x, hx⟩ := ih hs₃ hs
    exists x; simp only [mem_sdiff] at hx; simp only [mem_sdiff, Finset.mem_union, true_or, hx]
  . simp only [toAccessibleSystem, toFinsetOfList, mem_image, Set.mem_toFinset] at ha₂ hs₃
    let ⟨l₁, hl₁₁, hl₁₂⟩ := ha₂
    let ⟨l₂, hl₂₁, hl₂₂⟩ := hs₃
    let ⟨x, hx₁, hx₂⟩ := L.exchangeAxiom hl₁₁ hl₂₁ (by
      rw [← toFinset_card_of_nodup (mem_hereditary_nodup hl₁₁),
          ← toFinset_card_of_nodup (mem_hereditary_nodup hl₂₁),
          hl₁₂, hl₂₂, hs]
      simp [ha₁])
    exists x
    simp only [Finset.mem_union, Finset.mem_singleton, toAccessibleSystem, toFinsetOfList,
      mem_image, Set.mem_toFinset]
    have x_l₂_nodup := nodup_cons.mp (mem_hereditary_nodup hx₂)
    rw [← hl₁₂, ← hl₂₂]
    simp [hx₁, x_l₂_nodup]
    exists x :: l₂
    apply And.intro hx₂
    simp only [toFinset_cons, mem_toFinset, x_l₂_nodup, insert_eq, union_comm]

theorem fromLanguageToSystem'_greedoidSystemAxiom {L : GreedoidLanguage α} :
    greedoidSystemAxiom L.fromLanguageToSystem' :=
  ⟨fromLanguageToSystem'_containsEmpty,
    fromLanguageToSystem'_accessible,
    fromLanguageToSystem'_exchangeAxiom⟩

end GreedoidLanguage
