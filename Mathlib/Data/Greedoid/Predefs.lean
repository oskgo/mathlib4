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

theorem fromLanguageToSystem'_eq {L₁ L₂ : GreedoidLanguage α}
  (hL : L₁.fromLanguageToSystem' = L₂.fromLanguageToSystem') :
    L₁ = L₂ := by
  apply GreedoidLanguage.eq_of_veq
  ext l; constructor <;> intro h <;> induction' l with head l ih <;> simp only [containsEmpty] <;>
    have ⟨hhead, l_nodup⟩ := nodup_cons.mp (mem_hereditary_nodup h) <;>
    have ih := ih (mem_hereditary_containsTail h) <;>
    simp only [fromLanguageToSystem', toAccessibleSystem, ext_iff, mem_image,
      mem_toFinsetOfList, mem_toFinset] at hL
  . have ⟨l', hl'₁, hl'₂⟩ := (hL (head :: l).toFinset).mp ⟨head :: l, by simp [← ext_iff, h]⟩
    have l'_nodup := mem_hereditary_nodup hl'₁
    have hl'₃ : l'.toFinset = (head :: l).toFinset := by simp [ext_iff, hl'₂]
    have ⟨head', hhead'₁, hhead'₂⟩ := L₂.exchangeAxiom hl'₁ ih (by
      rw [← toFinset_card_of_nodup l_nodup, ← toFinset_card_of_nodup l'_nodup, hl'₃]
      simp [hhead])
    have : head = head' := by
      have := nodup_cons.mp (mem_hereditary_nodup hhead'₂)
      have := (hl'₂ _).mp hhead'₁
      simp only [toFinset_cons, mem_toFinset, mem_insert] at this
      tauto
    exact this ▸ hhead'₂
  . have ⟨l', hl'₁, hl'₂⟩ := (hL (head :: l).toFinset).mpr ⟨head :: l, by simp [← ext_iff, h]⟩
    have l'_nodup := mem_hereditary_nodup hl'₁
    have hl'₃ : l'.toFinset = (head :: l).toFinset := by simp [ext_iff, hl'₂]
    have ⟨head', hhead'₁, hhead'₂⟩ := L₁.exchangeAxiom hl'₁ ih (by
      rw [← toFinset_card_of_nodup l_nodup, ← toFinset_card_of_nodup l'_nodup, hl'₃]
      simp [hhead])
    have : head = head' := by
      have := nodup_cons.mp (mem_hereditary_nodup hhead'₂)
      have := (hl'₂ _).mp hhead'₁
      simp only [toFinset_cons, mem_toFinset, mem_insert] at this
      tauto
    exact this ▸ hhead'₂

noncomputable def fromLanguageToSystem (L : GreedoidLanguage α) : GreedoidSystem α :=
  ⟨L.fromLanguageToSystem',
   fromLanguageToSystem'_containsEmpty,
   fromLanguageToSystem'_accessible,
   fromLanguageToSystem'_exchangeAxiom⟩

theorem fromLanguageToSystem_eq {L₁ L₂ : GreedoidLanguage α}
  (hL : L₁.fromLanguageToSystem = L₂.fromLanguageToSystem) :
    L₁ = L₂ := by
  apply fromLanguageToSystem'_eq
  simp [fromLanguageToSystem] at hL
  exact hL

end GreedoidLanguage

namespace GreedoidSystem

variable {α : Type _} [DecidableEq α] [Fintype α]
variable {S : GreedoidSystem α}

open Nat List Finset Language GreedoidLanguage

def fromSystemToLanguage' (S : GreedoidSystem α) := toHereditaryLanguage S.feasibleSet

theorem fromSystemToLanguage'_nodup {l : List α} (hl : l ∈ S.fromSystemToLanguage') :
    l.Nodup :=
  toHereditaryLanguage_nodup hl

theorem fromSystemToLanguage'_containsEmpty :
    [] ∈ S.fromSystemToLanguage' :=
  toHereditaryLanguage_containsEmpty

theorem fromSystemToLanguage'_containsPrefix {l₁ l₂ : List α}
  (hl : l₂ ++ l₁ ∈ S.fromSystemToLanguage') :
    l₁ ∈ S.fromSystemToLanguage' :=
  toHereditaryLanguage_containsPrefix hl

theorem fromSystemToLanguage'_containsTail {head : α} {tail : List α}
  (hl : head :: tail ∈ S.fromSystemToLanguage') :
    tail ∈ S.fromSystemToLanguage' :=
  toHereditaryLanguage_containsTail hl

instance (S : GreedoidSystem α) : Hereditary S.fromSystemToLanguage' where
  nodup := fromSystemToLanguage'_nodup
  containsEmpty := fromSystemToLanguage'_containsEmpty
  containsPrefix := fromSystemToLanguage'_containsPrefix

theorem fromSystemToLanguage'_exchangeAxiom
  {l₁ : List α} (hl₁ : l₁ ∈ S.fromSystemToLanguage')
  {l₂ : List α} (hl₂ : l₂ ∈ S.fromSystemToLanguage')
  (hl : l₁.length > l₂.length) :
    ∃ x ∈ l₁, x :: l₂ ∈ S.fromSystemToLanguage' := by
  simp [fromSystemToLanguage', toHereditaryLanguage] at *
  rw [Set.mem_def] at hl₁ hl₂
  have ⟨x, hx₁, hx₂⟩ := S.exchangeAxiom (hl₁.2 (suffix_refl l₁)) (hl₂.2 (suffix_refl l₂))
    ((toFinset_card_of_nodup hl₁.1) ▸ (toFinset_card_of_nodup hl₂.1) ▸ hl)
  simp only [mem_sdiff, mem_toFinset] at hx₁
  exists x
  rw [Set.mem_def]
  simp only [hx₁, nodup_cons, not_false_eq_true, hl₂, true_and]
  intro l' hl'
  rw [suffix_cons_iff] at hl'
  apply hl'.elim _ (fun h => hl₂.2 h)
  intro hl'
  rw [union_comm, ← insert_eq] at hx₂
  simp only [hl', toFinset_cons, mem_toFinset, hx₂]

theorem fromSystemToLanguage'_greedoidLanguageAxiom :
    greedoidLanguageAxiom S.fromSystemToLanguage' :=
  ⟨fromSystemToLanguage'_nodup,
   fromSystemToLanguage'_containsEmpty,
   fromSystemToLanguage'_containsPrefix,
   fromSystemToLanguage'_exchangeAxiom⟩

theorem fromSystemToLanguage'_eq {S₁ S₂ : GreedoidSystem α}
  (hS : S₁.fromSystemToLanguage' = S₂.fromSystemToLanguage') :
    S₁ = S₂ := by
  simp [fromSystemToLanguage', toHereditaryLanguage] at hS
  rw [Set.ext_iff] at hS
  simp only [Set.mem_def, and_congr_right_iff] at hS
  apply GreedoidSystem.eq_of_veq
  ext s
  constructor <;> intro h
  . sorry
  . sorry

def fromSystemToLanguage (S : GreedoidSystem α) : GreedoidLanguage α :=
  ⟨S.fromSystemToLanguage',
   fromSystemToLanguage'_nodup,
   fromSystemToLanguage'_containsEmpty,
   fromSystemToLanguage'_containsPrefix,
   fromSystemToLanguage'_exchangeAxiom⟩

theorem fromSystemToLanguage_eq {S₁ S₂ : GreedoidSystem α}
  (hS : S₁.fromSystemToLanguage = S₂.fromSystemToLanguage) :
    S₁ = S₂ := by
  apply fromSystemToLanguage'_eq
  simp [fromSystemToLanguage] at hS
  exact hS

end GreedoidSystem

namespace Greedoid

variable {α : Type _} [DecidableEq α] [Fintype α]
variable {L : GreedoidLanguage α}
variable {S : GreedoidSystem α}

open Nat List Finset GreedoidLanguage GreedoidSystem

@[simp]
theorem fromSystemToLanguage_fromLanguageToSystem_eq :
    S.fromSystemToLanguage.fromLanguageToSystem = S := by
  sorry

@[simp]
theorem fromLanguageToSystem_fromSystemToLanguage_eq :
    L.fromLanguageToSystem.fromSystemToLanguage = L := by
  sorry

-- TODO: This instance should be under `GreedoidLanguage` namespace.
instance {α : Type _} [DecidableEq α] [Fintype α] : Fintype (GreedoidLanguage α) :=
  Fintype.ofBijective GreedoidSystem.fromSystemToLanguage (Function.bijective_iff_has_inverse.mpr
    ⟨GreedoidLanguage.fromLanguageToSystem, by
      simp [Function.LeftInverse], by
      simp [Function.RightInverse, Function.LeftInverse]⟩)

def relatedLanguageSystem' (L : GreedoidLanguage α) (S : GreedoidSystem α) :=
  S.feasibleSet = L.fromLanguageToSystem' ∧ L.language = S.fromSystemToLanguage'

def relatedLanguageSystem (L : GreedoidLanguage α) (S : GreedoidSystem α) :=
  S = L.fromLanguageToSystem ∧ L = S.fromSystemToLanguage

@[simp]
theorem relatedLanguageSystem'_iff_relatedLanguageSystem :
    relatedLanguageSystem' L S ↔ relatedLanguageSystem L S := by
  sorry

theorem relatedLanguageSystem_eq
  {L₁ L₂ : GreedoidLanguage α} {S₁ S₂ : GreedoidSystem α}
  (h₁ : relatedLanguageSystem L₁ S₁)
  (h₂ : relatedLanguageSystem L₂ S₂) :
    L₁ = L₂ ↔ S₁ = S₂ :=
  ⟨fun h => fromSystemToLanguage_eq ((h ▸ h₁.2) ▸ h₂.2),
   fun h => fromLanguageToSystem_eq ((h ▸ h₁.1) ▸ h₂.1)⟩

theorem relatedLanguageSystem_of_fromLanguageToSystem :
    relatedLanguageSystem L L.fromLanguageToSystem := by
  simp [relatedLanguageSystem]

theorem relatedLanguageSystem_of_fromSystemToLanguage :
    relatedLanguageSystem S.fromSystemToLanguage S := by
  simp [relatedLanguageSystem]

theorem toFinset_mem_greedoidSystem_of_mem_greedoidLanguage
  (hrelated : relatedLanguageSystem L S)
  {l : List α} (hl : l ∈ L.language) :
    l.toFinset ∈ S.feasibleSet := by
  sorry

theorem exists_word_mem_greedoidLanguage_of_mem_greedoidSystem
  (hrelated : relatedLanguageSystem L S)
  {s : Finset α} (hs : s ∈ S.feasibleSet) :
    ∃ l ∈ L.language, l.toFinset = s := by
  sorry

end Greedoid
