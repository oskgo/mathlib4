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
* a term `e : ε` can be interpreted via `bound a e : α` as a lower bound for `a`, and
* we can ask for an improved lower bound via `improve a e : Option ε`.

The value `a` in `α` that we are estimating is hidden inside a `Thunk` to avoid evaluation.
 -/
class EstimatorData (a : Thunk α) (ε : Type _) where
  bound : ε → α
  improve : ε → Option ε

/--
Given `[Estimator a ε]`
* we have `bound a e ≤ a`, and
* `improve a e` returns none iff `bound a e = a`, and otherwise it returns a strictly better bound.
-/
class Estimator [Preorder α] (a : Thunk α) (ε : Type _) extends EstimatorData a ε where
  bound_le e : bound e ≤ a.get
  improve_spec e : match improve e with
    | none => bound e = a.get
    | some e' => bound e < bound e'

open EstimatorData

attribute [local instance] WellFoundedGT.toWellFoundedRelation

/-- Improve an estimate until it satisfies a predicate, or stop if we reach the exact value. -/
def Estimator.improveUntil [PartialOrder α] [∀ a : α, WellFoundedGT { x // x ≤ a }]
    (a : Thunk α) (p : α → Bool) [Estimator a ε] (e : ε) : Option ε :=
  if p (bound a e) then
    return e
  else
    match improve a e, improve_spec e with
    | none, _ => none
    | some e', _ =>
      Estimator.improveUntil a p e'
termination_by Estimator.improveUntil p I e => (⟨_, bound_le e⟩ : { x // x ≤ a.get })

variable [PartialOrder α] [∀ a : α, WellFoundedGT { x // x ≤ a }]

/--
If `Estimator.improveUntil a p e` returns `some e'`, then `bound a e'` satisfies `p`.
Otherwise, that value `a` must not satisfy `p`.
-/
theorem Estimator.improveUntil_spec
    (a : Thunk α) (p : α → Bool) [Estimator a ε] (e : ε) :
    match Estimator.improveUntil a p e with
    | none => ¬ p a.get
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
termination_by Estimator.improveUntil_spec p I e => (⟨_, bound_le e⟩ : { x // x ≤ a.get })

/--
An estimator for `(a, b)` can be turned into an estimator for `a`,
simply by repeatedly running `improve` until the first factor "improves".
The hypothesis that `>` is well-founded on `{ q // q ≤ (a, b) }` ensures this terminates.
-/
structure Estimator.fst [Preorder α] [Preorder β]
    (p : Thunk (α × β)) (ε : Type _) [Estimator p ε] where
  inner : ε

/-- The product of two thunks. -/
def Thunk.prod (a : Thunk α) (b : Thunk β) : Thunk (α × β) := Thunk.mk fun _ => (a.get, b.get)

@[simp] lemma Thunk.prod_get_fst : (Thunk.prod a b).get.1 = a.get := rfl
@[simp] lemma Thunk.prod_get_snd : (Thunk.prod a b).get.2 = b.get := rfl

instance [PartialOrder α] [DecidableRel ((· : α) < ·)] [PartialOrder β] {a : Thunk α} {b : Thunk β}
    (ε : Type _) [Estimator (a.prod b) ε] [∀ (p : α × β), WellFoundedGT { q // q ≤ p }] :
    EstimatorData a (Estimator.fst (a.prod b) ε) where
  bound e := (bound (a.prod b) e.inner).1
  improve e :=
    let bd := (bound (a.prod b) e.inner).1
    Estimator.improveUntil (a.prod b) (fun p => bd < p.1) e.inner |>.map Estimator.fst.mk

instance instEstimatorFst [PartialOrder α] [DecidableRel ((· : α) < ·)] [PartialOrder β]
    [∀ (p : α × β), WellFoundedGT { q // q ≤ p }]
    (a : Thunk α) (b : Thunk β) (ε : Type _) [Estimator (a.prod b) ε] :
    Estimator a (Estimator.fst (a.prod b) ε) where
  bound_le e := (Estimator.bound_le e.inner : bound (a.prod b) e.inner ≤ (a.get, b.get)).1
  improve_spec e := by
    let bd := (bound (a.prod b) e.inner).1
    have := Estimator.improveUntil_spec (a.prod b) (fun p => bd < p.1) e.inner
    revert this
    simp only [EstimatorData.improve, decide_eq_true_eq]
    match Estimator.improveUntil (a.prod b) _ _ with
    | none =>
      simp only [Option.map_none']
      exact fun w =>
        eq_of_le_of_not_lt
          (Estimator.bound_le e.inner : bound (a.prod b) e.inner ≤ (a.get, b.get)).1 w
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
def EstimatorQueue (β : Type _) (prio : β → Thunk ℕ) (ε : β → Type _) : Type _ :=
  List (Σ b, ε b)

instance : EmptyCollection (EstimatorQueue β p ε) := ⟨[]⟩
instance : Inhabited (EstimatorQueue β p ε) := ⟨∅⟩

namespace EstimatorQueue

variable {prio : β → Thunk ℕ} {ε : β → Type _} [∀ b, Estimator (prio b) (ε b)] [∀ b, Bot (ε b)]

/--
Add a pair, consisting of an element and an estimate of its priority, to an estimator queue,
placing it in the first position where its estimate is less than or equal to the next estimate.
-/
def push (Q : EstimatorQueue β prio ε) (b : β) (p : ε b := ⊥) :
    EstimatorQueue β prio ε :=
  match Q, (⟨b, p⟩ : Σ b, ε b) with
  | [], p => [p]
  | ⟨b, e⟩ :: (t : EstimatorQueue β prio ε), ⟨b', e'⟩ =>
    if bound (prio b') e' ≤ bound (prio b) e then
      ⟨b', e'⟩ :: ⟨b, e⟩ :: t
    else
      ⟨b, e⟩ :: t.push b' e'

def pushAll (Q : EstimatorQueue β prio ε) (bs : List β) : EstimatorQueue β prio ε :=
  bs.foldl (init := Q) fun Q' b => Q'.push b

/--
Assuming the elements in the estimator queue have non-decreasing bounds,
pop off the element with the lowest priority, along with its priority.

We implement this by attempting to improve the estimate for the first element in the list,
until it is strictly greater than the estimate for the second element in the list.
If this fails, we have shown the first element has (equal) lowest priority, so we return that.
If it succeeds, we swap the order of the first two elements, and try again.

We could give a termination proof, based on the sum of the estimates,
but don't for now.
-/
partial def popWithPriority (Q : EstimatorQueue β prio ε) :
    Option (β × ℕ) × EstimatorQueue β prio ε :=
  match Q with
  | [] => (none, [])
  | [⟨b, e⟩] => ((b, bound (prio b) e), [])
  | ⟨b₁, e₁⟩ :: ⟨b₂, e₂⟩ :: (t : EstimatorQueue β prio ε) =>
      match improveUntil (prio b₁) (bound (prio b₂) e₂ < ·) e₁ with
      | none => ((b₁, bound (prio b₁) e₁), ⟨b₂, e₂⟩ :: t)
      | some e₁' => EstimatorQueue.popWithPriority (⟨b₂, e₂⟩ :: t.push b₁ e₁')

/--
Assuming the elements in the estimator queue have non-decreasing bounds,
pop off the element with the lowest priority.
-/
def pop (Q : EstimatorQueue β prio ε) : Option β × EstimatorQueue β prio ε :=
  match Q.popWithPriority with
  | (none, Q) => (none, Q)
  | (some (b, _), Q) => (some b, Q)

partial def toListWithPriority (Q : EstimatorQueue β prio ε) : List (β × ℕ) :=
  match Q.popWithPriority with
  | (none, _) => []
  | (some p, Q) => p :: Q.toListWithPriority

partial def toList (Q : EstimatorQueue β prio ε) : List β :=
  match Q.pop with
  | (none, _) => []
  | (some b, Q) => b :: Q.toList
