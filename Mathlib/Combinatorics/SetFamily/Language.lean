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
import Mathlib.Computability.Language
import Mathlib.Combinatorics.SetFamily.Accessible

namespace Language

-- Here, word and list are identical.

/-- Simple language are words which only contain words without duplicates. -/
class Simple {α : Type _} [DecidableEq α] (Lang : Language α) where
  /-- Any word inside a simple language does not contain a duplicate. -/
  nodup : ∀ {l}, l ∈ Lang → l.Nodup

section Simple

variable {α : Type _} [DecidableEq α]
variable {Lang : Language α} [Simple Lang]

open Nat List Finset

theorem mem_simple_nodup {l : List α} (hl : l ∈ Lang) : l.Nodup := Simple.nodup hl

theorem simple_fintype_finite [Fintype α] : Lang.Finite :=
  let s : Set (List α) := ⋃ (y : Finset α), ↑y.val.lists
  let hs : s.Finite := Set.finite_iUnion (fun _ => finite_toSet _)
  Set.Finite.subset hs (by
    intro l hl
    simp
    exists l.toFinset
    simp only [toFinset_val, mem_simple_nodup hl, Nodup.dedup])

/-- Every simple languages are finite under finite type. -/
noncomputable instance fintypeLanguage [Fintype α] :
    Fintype Lang.Elem :=
  Set.Finite.fintype simple_fintype_finite

/-- Convert simple `Lang` from `Language α` to `Finset (List α)`. -/
noncomputable def toFinsetOfList [Fintype α] (Lang : Language α) [Simple Lang] :
    Finset (List α) :=
  Set.toFinset Lang

end Simple

/-- Normal language contains no loops; every alphabet is in some word in the language. -/
class Normal {α : Type _} [DecidableEq α] (Lang : Language α) extends Simple Lang where
  /-- Normal language contains no loops. -/
  noLoops : ∀ {a}, ∃ l ∈ Lang, a ∈ l

section Normal

variable {α : Type _} [DecidableEq α]
variable {Lang : Language α} [Normal Lang]

open Nat List Finset

theorem mem_normal_nodup {l : List α} (hl : l ∈ Lang) : l.Nodup := Normal.toSimple.nodup hl

theorem mem_normal_noLoops {a : α} : ∃ l ∈ Lang, a ∈ l := Normal.noLoops

theorem normal_fintype_finite [Fintype α] : Lang.Finite := simple_fintype_finite

end Normal

/-- Hereditary language contains the emptyset and the prefix of every word in the language. -/
class Hereditary {α : Type _} [DecidableEq α] (Lang : Language α) extends Simple Lang where
  /-- Hereditary language contains the empty word. -/
  containsEmpty : [] ∈ Lang
  /-- Suffix of each word in hereditary language is in the language. -/
  containsPrefix : ∀ {l₁ l₂}, l₂ ++ l₁ ∈ Lang → l₁ ∈ Lang

section Hereditary

variable {α : Type _} [DecidableEq α]
variable {Lang : Language α} [Hereditary Lang]

open Nat List Finset

theorem mem_hereditary_nodup {l : List α} (hl : l ∈ Lang) : l.Nodup := Hereditary.toSimple.nodup hl

theorem mem_hereditary_containsEmpty : [] ∈ Lang := Hereditary.containsEmpty

theorem mem_hereditary_containsPrefix {l₁ l₂ : List α} (hl : l₂ ++ l₁ ∈ Lang) :
    l₁ ∈ Lang :=
  Hereditary.containsPrefix hl

theorem mem_hereditary_containsTail {head : α} {tail : List α} (h : head :: tail ∈ Lang) :
    tail ∈ Lang :=
  @mem_hereditary_containsPrefix _ _ _ _ tail [head] (singleton_append ▸ h)

theorem hereditary_fintype_finite [Fintype α] : Lang.Finite := simple_fintype_finite

/-- Converts hereditary language `Lang` to set system. -/
noncomputable def toAccessibleSystem [Fintype α] (Lang : Language α) [Hereditary Lang] :
    Finset (Finset α) :=
  Lang.toFinsetOfList.image fun l => l.toFinset

theorem toAccessibleSystem_containsEmpty [Fintype α] : ∅ ∈ Lang.toAccessibleSystem := by
  simp [toAccessibleSystem, toFinsetOfList, Set.toFinset]
  exact Hereditary.containsEmpty

theorem toAccessibleSystem_accessible [Fintype α]
  {s : Finset α} (hs₁ : s ∈ Lang.toAccessibleSystem) (hs₂ : s ≠ ∅) :
    ∃ x ∈ s, s \ {x} ∈ Lang.toAccessibleSystem := by
  simp [toAccessibleSystem, toFinsetOfList, Set.toFinset] at *
  have ⟨l, hl₁, hl₂⟩ := hs₁
  by_cases hl₄ : l = []
  . rw [hl₄] at hl₂
    rw [← hl₂] at hs₂
    contradiction
  . cases' l with head l <;> try contradiction
    exists head
    simp [← hl₂]
    exists l
    apply And.intro (mem_hereditary_containsTail hl₁)
    rw [insert_sdiff_of_mem _ (mem_singleton_self head)]
    symm; simp [sdiff_eq_self, nodup_cons.mp (mem_hereditary_nodup hl₁)]

instance [Fintype α] (Lang : Language α) [Hereditary Lang] :
    Accessible Lang.toAccessibleSystem where
  containsEmpty := toAccessibleSystem_containsEmpty
  accessible := toAccessibleSystem_accessible

end Hereditary

end Language

section Accessible

variable {α : Type _} [DecidableEq α]
variable {Sys : Finset (Finset α)} [Accessible Sys]
variable {s : Finset α} (hs₀ : s ∈ Sys)

open Nat List Finset Language

/-- Converts (accessible) `Sys` to hereditary language. -/
def toHereditaryLanguage (Sys : Finset (Finset α)) :
    Language α :=
  fun l => l.Nodup ∧ ∀ {l'}, l' <:+ l → l'.toFinset ∈ Sys

theorem toHereditaryLanguage_nodup {l : List α} (hl : l ∈ toHereditaryLanguage Sys) :
    l.Nodup := hl.1

theorem toHereditaryLanguage_containsEmpty :
    [] ∈ toHereditaryLanguage Sys := by
  simp only [toHereditaryLanguage]; constructor <;> simp [accessible_containsEmpty]

theorem toHereditaryLanguage_containsPrefix {l₁ l₂ : List α}
  (hl : l₂ ++ l₁ ∈ toHereditaryLanguage Sys) :
    l₁ ∈ toHereditaryLanguage Sys := by
  simp only [toHereditaryLanguage] at *
  apply And.intro (Nodup.of_append_right hl.1)
  exact fun h => hl.2 (isSuffix.trans h (suffix_append _ _))

theorem toHereditaryLanguage_containsTail {head : α} {tail : List α}
  (hl : head :: tail ∈ toHereditaryLanguage Sys) :
    tail ∈ toHereditaryLanguage Sys :=
  @toHereditaryLanguage_containsPrefix _ _ _ tail [head] hl

instance (Sys : Finset (Finset α)) [Accessible Sys] : Hereditary (toHereditaryLanguage Sys) where
  nodup := toHereditaryLanguage_nodup
  containsEmpty := toHereditaryLanguage_containsEmpty
  containsPrefix := toHereditaryLanguage_containsPrefix

end Accessible
