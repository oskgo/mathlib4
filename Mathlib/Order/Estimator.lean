/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Order.RelClasses
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Sub.Prod
import Mathlib.Data.Nat.Order.Basic

/--
Given `[EstimatorData a ε]`
* a term `e : ε` can be interpreted via `bound a e` as a lower bound for `a`, and
* we can ask for an improved lower bound via `improve a e`.
 -/
class EstimatorData (a : α) (ε : Type _) where
  bound : ε → α
  improve : ε → Option ε

/--
Given `[Estimator a ε]`
* we have `bound a e ≤ a`, and
* `improve a e` returns none iff `bound a e = a`, and otherwise it returns a strictly better bound.
-/
class Estimator [Preorder α] (a : α) (ε : Type _) extends EstimatorData a ε where
  bound_le e : bound e ≤ a
  improve_spec e : match improve e with
    | none => bound e = a
    | some e' => bound e < bound e'

open EstimatorData

-- These typeclasses are satified for the two cases I'm interested in, `ℕ` and `ℕ × ℕ`.
variable {α : Type _} [AddCommSemigroup α] [PartialOrder α] [ExistsAddOfLE α]
  [CovariantClass α α (· + ·) (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]
  [Sub α] [OrderedSub α]

attribute [local instance] WellFoundedLT.toWellFoundedRelation

/-- Improve an estimate until it satisfies a predicate, or stop if we reach the exact value. -/
def Estimator.improveUntil [WellFoundedLT α]
    (a : α) (p : α → Bool) [Estimator a ε] (e : ε) : Option ε :=
  if p (bound a e) then
    return e
  else
    match improve a e, improve_spec e with
    | none, _ => none
    | some e', lt =>
      have : a - bound a e' < a - bound a e :=
        tsub_lt_tsub_left_of_le (bound_le e') lt
      Estimator.improveUntil a p e'
termination_by Estimator.improveUntil p I e => a - bound a e

variable [WellFoundedLT α]

/--
If `Estimator.improveUntil a p e` returns `some e'`, then `bound a e'` satisfies `p`.
Otherwise, that value `a` must not satisfy `p`.
-/
theorem Estimator.improveUntil_spec
    (a : α) (p : α → Bool) [Estimator a ε] (e : ε) :
    match Estimator.improveUntil a p e with
    | none => ¬ p a
    | some e' => p (bound a e') := by
  rw [Estimator.improveUntil]
  split_ifs with h
  · exact h
  · match improve a e, improve_spec e with
    | none, eq =>
      simp only [Bool.not_eq_true]
      rw [eq] at h
      exact Bool.bool_eq_false h
    | some e', lt =>
      have : a - bound a e' < a - bound a e :=
        tsub_lt_tsub_left_of_le (bound_le e') lt
      exact Estimator.improveUntil_spec a p e'
termination_by Estimator.improveUntil_spec p I e => a - bound a e

open Estimator

set_option linter.unusedVariables false in
/--
An estimator queue is a (lowest-first) priority queue for which we lazily compute priorities.
We store pairs `Σ b, ε b`, where `b : β` is the queue element, and `ε b` is a lower bound estimate
for its priority.

When adding elements we place a pair in the first place such that the estimates are non-decreasing.
When removing elements we recursively improve the estimates to be sure that the element we return
has minimal priority.
-/
def EstimatorQueue (β : Type _) (prio : β → ℕ) (ε : β → Type _) : Type _ :=
  List (Σ b, ε b)

instance {prio : β → ℕ} {ε : β → Type _} : Inhabited (EstimatorQueue β prio ε) := ⟨[]⟩

/--
Add a pair, consisting of an element and an estimate of its priority, to an estimator queue,
placing it in the first position where its estimate is less than or equal to the next estimate.
-/
def EstimatorQueue.push {prio : β → ℕ} {ε : β → Type _} [∀ b, Estimator (prio b) (ε b)]
    (Q : EstimatorQueue β prio ε) (p : Σ b, ε b) : EstimatorQueue β prio ε :=
  match Q, p with
  | [], p => [p]
  | ⟨b, e⟩ :: (t : EstimatorQueue β prio ε), ⟨b', e'⟩ =>
    if bound (prio b') e' ≤ bound (prio b) e then
      ⟨b', e'⟩ :: ⟨b, e⟩ :: t
    else
      ⟨b, e⟩ :: t.push ⟨b', e'⟩

/--
Assuming the elements in the estimator queue have non-decreasing bounds,
pop off the element with the lowest priority.

We implement this by attempting to improve the estimate for the first element in the list,
until it is strictly greater than the estimate for the second element in the list.
If this fails, we have shown the first element has (equal) lowest priority, so we return that.
If it succeeds, we swap the order of the first two elements, and try again.

We could give a termination proof, based on the sum of the estimates,
but don't for now.
-/
partial def EstimatorQueue.pop {prio : β → ℕ} {ε : β → Type _} [∀ b, Estimator (prio b) (ε b)]
    (Q : EstimatorQueue β prio ε) : Option β × EstimatorQueue β prio ε :=
  match Q with
  | [] => (none, [])
  | [⟨b, _⟩] => (b, [])
  | ⟨b₁, e₁⟩ :: ⟨b₂, e₂⟩ :: (t : EstimatorQueue β prio ε) =>
      match improveUntil (prio b₁) (bound (prio b₂) e₂ < ·) e₁ with
      | none => (b₁, ⟨b₂, e₂⟩ :: t)
      | some e₁' => EstimatorQueue.pop (⟨b₂, e₂⟩ :: t.push ⟨b₁, e₁'⟩)
