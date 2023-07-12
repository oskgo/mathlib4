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

/-- List of axioms in `GreedoidLanguage` -/
def greedoidLanguageAxiom {α : Type _} (Lang : Language α) :=
  (∀ {l}, l ∈ Lang → l.Nodup) ∧
  ([] ∈ Lang) ∧
  (∀ {l₁ l₂ : List α}, l₂ ++ l₁ ∈ Lang → l₁ ∈ Lang) ∧
  ({l₁ : List α} → l₁ ∈ Lang → {l₂ : List α} → l₂ ∈ Lang →
    l₁.length > l₂.length → ∃ x ∈ l₁, x :: l₂ ∈ Lang)

protected theorem GreedoidLanguage.eq_of_veq {α : Type _} [Fintype α] :
    ∀ {L₁ L₂ : GreedoidLanguage α}, L₁.language = L₂.language → L₁ = L₂
  | ⟨l₁, _, _, _, _⟩, ⟨l₂, _, _, _, _⟩, h => by cases h; rfl

theorem greedoidLanguageAxiom_greedoidLangauge {α : Type _} [Fintype α] {L : GreedoidLanguage α} :
    greedoidLanguageAxiom L.language :=
  ⟨L.nodup, L.containsEmpty, L.containsPrefix, L.exchangeAxiom⟩

instance {α : Type _} [Fintype α] [DecidableEq α] : Fintype (GreedoidLanguage α) where
  elems :=
    let simple_lists : Set (List α) := ⋃ (y : Finset α), ↑y.val.lists
    let simple_languages : Finset (Language α) :=
      @Set.toFinset _
        (𝒫 simple_lists ∩ greedoidLanguageAxiom)
        (Set.fintypeInterOfLeft _ _)
    --(fun Lang => (⟨Lang, sorry, sorry, sorry, sorry⟩ : GreedoidLanguage α)) '' simple_languages
    sorry
  complete := sorry
