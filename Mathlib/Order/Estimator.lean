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
import Mathlib.Order.LocallyFinite
import Mathlib.Data.Nat.Interval

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

attribute [local instance] WellFoundedGT.toWellFoundedRelation

/-- Improve an estimate until it satisfies a predicate, or stop if we reach the exact value. -/
def Estimator.improveUntil [PartialOrder α] [∀ a : α, WellFoundedGT { x // x ≤ a }]
    (a : α) (p : α → Bool) [Estimator a ε] (e : ε) : Option ε :=
  if p (bound a e) then
    return e
  else
    match improve a e, improve_spec e with
    | none, _ => none
    | some e', _ =>
      Estimator.improveUntil a p e'
termination_by Estimator.improveUntil p I e => (⟨_, bound_le e⟩ : { x // x ≤ a })

variable [PartialOrder α] [∀ a : α, WellFoundedGT { x // x ≤ a }]

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
    | some e', _ =>
      exact Estimator.improveUntil_spec a p e'
termination_by Estimator.improveUntil_spec p I e => (⟨_, bound_le e⟩ : { x // x ≤ a })

/--
An estimator for `(a, b)` can be turned into an estimator for `a`,
simply by repeatedly running `improve` until the first factor "improves".
With the hypothesis that `>` is well-founded on `{ q // q ≤ (a, b) }` ensures this terminates.
-/
structure Estimator.fst [Preorder α] [Preorder β] (p : α × β) (ε : Type _) [Estimator p ε] where
  inner : ε

instance [PartialOrder α] [DecidableRel ((· : α) < ·)] [PartialOrder β] {a : α} {b : β}
    (ε : Type _) [Estimator (a, b) ε] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }] :
    EstimatorData a (Estimator.fst (a, b) ε) where
  bound e := (bound (a, b) e.inner).1
  improve e :=
    let bd := (bound (a, b) e.inner).1
    Estimator.improveUntil (a, b) (fun p => bd < p.1) e.inner |>.map Estimator.fst.mk

instance [PartialOrder α] [DecidableRel ((· : α) < ·)] [PartialOrder β] {a : α} {b : β}
    (ε : Type _) [Estimator (a, b) ε] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }] :
    Estimator a (Estimator.fst (a, b) ε) where
  bound_le e := (Estimator.bound_le e.inner : bound (a, b) e.inner ≤ (a, b)).1
  improve_spec e := by
    let bd := (bound (a, b) e.inner).1
    have := Estimator.improveUntil_spec (a, b) (fun p => bd < p.1) e.inner
    revert this
    simp only [EstimatorData.improve, decide_eq_true_eq]
    match Estimator.improveUntil (a, b) _ _ with
    | none =>
      simp only [Option.map_none']
      exact fun w =>
        eq_of_le_of_not_lt (Estimator.bound_le e.inner : bound (a, b) e.inner ≤ (a, b)).1 w
    | some e' => exact fun w => w

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
