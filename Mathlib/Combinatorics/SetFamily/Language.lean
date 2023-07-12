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
class Simple {α : Type _} [DecidableEq α] (L : Language α) where
  /-- Any word inside a simple language does not contain a duplicate. -/
  nodup : ∀ {l}, l ∈ L → List.Nodup l

section Simple

variable {α : Type _} [DecidableEq α]
variable {L : Language α} [Simple L]

open Nat List Finset

theorem mem_simple_nodup {l : List α} (hl : l ∈ L) : l.Nodup := Simple.nodup hl

theorem simple_fintype_finite [Fintype α] : L.Finite :=
  let s : Set (List α) := ⋃ (y : Finset α), ↑y.val.lists
  let hs : s.Finite := Set.finite_iUnion (fun _ => finite_toSet _)
  Set.Finite.subset hs (by
    intro l hl
    simp
    exists l.toFinset
    simp only [toFinset_val, mem_simple_nodup hl, Nodup.dedup])

protected noncomputable def Simple.fintype [Fintype α] : Fintype L.Elem :=
  Set.Finite.fintype simple_fintype_finite

noncomputable def toFinsetOfList [Fintype α] (L : Language α) [Simple L] :
    Finset (List α) :=
  @Set.toFinset _ L Simple.fintype

end Simple

/-- Normal language contains no loops; every alphabet is in some word in the language. -/
class Normal {α : Type _} [DecidableEq α] (L : Language α) extends Simple L where
  /-- Normal language contains no loops. -/
  noLoops : ∀ {a}, ∃ w ∈ L, a ∈ w

section Normal

variable {α : Type _} [DecidableEq α]
variable {L : Language α} [Normal L]

open Nat List Finset

theorem mem_normal_nodup {l : List α} (hl : l ∈ L) : l.Nodup := Normal.toSimple.nodup hl

theorem mem_normal_noLoops {a : α} : ∃ w ∈ L, a ∈ w := Normal.noLoops

theorem normal_fintype_finite [Fintype α] : L.Finite := simple_fintype_finite

end Normal

/-- Hereditary language contains the emptyset and the prefix of every word in the language. -/
class Hereditary {α : Type _} [DecidableEq α] (L : Language α) extends Simple L where
  /-- Hereditary language contains the empty word. -/
  containsEmpty : [] ∈ L
  /-- Suffix of each word in hereditary language is in the language. -/
  containsPrefix : ∀ {w₁ w₂}, w₂ ++ w₁ ∈ L → w₁ ∈ L

section Hereditary

variable {α : Type _} [DecidableEq α]
variable {L : Language α} [Hereditary L]

open Nat List Finset

theorem mem_hereditary_nodup {l : List α} (hl : l ∈ L) : l.Nodup := Hereditary.toSimple.nodup hl

theorem mem_hereditary_containsEmpty : [] ∈ L := Hereditary.containsEmpty

theorem mem_hereditary_containsPrefix {w₁ w₂ : List α} (hw : w₂ ++ w₁ ∈ L) :
    w₁ ∈ L :=
  Hereditary.containsPrefix hw

theorem hereditary_fintype_finite [Fintype α] : L.Finite := simple_fintype_finite

noncomputable def toAccessibleSystem [Fintype α] (L : Language α) [Hereditary L] :
    Finset (Finset α) :=
  L.toFinsetOfList.image fun l => l.toFinset

theorem toAccessibleSystem_containsEmpty [Fintype α] : ∅ ∈ L.toAccessibleSystem := by
  simp [toAccessibleSystem, toFinsetOfList, Set.toFinset]
  exists Hereditary.containsEmpty
  simp only [mem_univ _]

theorem toAccessibleSystem_accessible [Fintype α]
  {s : Finset α} (hs₁ : s ∈ L.toAccessibleSystem) (hs₂ : s ≠ ∅) :
    ∃ x ∈ s, s \ {x} ∈ L.toAccessibleSystem := by
  simp [toAccessibleSystem, toFinsetOfList, Set.toFinset] at *
  have ⟨l, ⟨hl₁, hl₂⟩, hl₃⟩ := hs₁
  by_cases hl₄ : l = []
  . rw [hl₄] at hl₃
    rw [← hl₃] at hs₂
    contradiction
  . cases' l with head l <;> try contradiction
    exists head
    simp [← hl₃]
    exists l
    constructor
    . exists (mem_hereditary_containsPrefix (by simp; exact hl₁ : [head] ++ l ∈ L))
      simp only [mem_univ _]
    . rw [insert_sdiff_of_mem _ (mem_singleton_self head)]
      symm
      simp [sdiff_eq_self, nodup_cons.mp (mem_hereditary_nodup hl₁)]

instance [Fintype α] (L : Language α) [Hereditary L] : Accessible L.toAccessibleSystem where
  containsEmpty := toAccessibleSystem_containsEmpty
  accessible := toAccessibleSystem_accessible

end Hereditary

end Language
