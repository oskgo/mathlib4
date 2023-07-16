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
import Mathlib.Data.Greedoid.Predefs

/-- Merging of language and system version of greedoid.
    This will (potentially) help `Greedoid` cover theorems written in
    both language and systems. -/
structure Greedoid (α : Type _) [Fintype α] [DecidableEq α] where
  /-- Greedoid as a language. -/
  language : GreedoidLanguage α
  /-- Greedoid as a system. -/
  system : GreedoidSystem α
  /-- `language` and `system` are related. -/
  related : Greedoid.relatedLanguageSystem language system
