/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Order.Estimator
import Mathlib.Data.Nat.Interval

open EstimatorData Estimator

set_option linter.unusedVariables false in
/--
An estimator queue is a (lowest-first) priority queue for which we lazily compute priorities.
We store pairs `Σ b, ε b`, where `b : β` is the queue element, and `ε b` is a lower bound estimate
for its priority.

When adding elements we place a pair in the first place such that the estimates are non-decreasing.
When removing elements we recursively improve the estimates to be sure that the element we return
has minimal priority.
-/
def EstimatorQueue (β : Type u) (prio : β → Thunk ℕ) (ε : β → Type u) : Type _ :=
  List (Σ b, ε b)

instance : EmptyCollection (EstimatorQueue β p ε) := ⟨[]⟩
instance : Inhabited (EstimatorQueue β p ε) := ⟨∅⟩

namespace EstimatorQueue

variable {prio : β → Thunk ℕ} {ε : β → Type u} [∀ b, Estimator (prio b) (ε b)] [∀ b, Bot (ε b)]

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
partial def popWithBound (Q : EstimatorQueue β prio ε) :
    Option (((b : β) × ε b) × EstimatorQueue β prio ε) :=
  match Q with
  | [] => none
  | [⟨b, e⟩] => some (⟨b, e⟩, [])
  | ⟨b₁, e₁⟩ :: ⟨b₂, e₂⟩ :: (t : EstimatorQueue β prio ε) =>
      match improveUntil (prio b₁) (bound (prio b₂) e₂ < ·) e₁ with
      | .error none => some (⟨b₁, e₁⟩, ⟨b₂, e₂⟩ :: t)
      | .error (some e₁') => some (⟨b₁, e₁'⟩, ⟨b₂, e₂⟩ :: t)
      | .ok e₁' => EstimatorQueue.popWithBound (⟨b₂, e₂⟩ :: t.push b₁ e₁')

partial def popWithPriority (Q : EstimatorQueue β prio ε) :
    Option ((β × ℕ) × EstimatorQueue β prio ε) :=
  match Q.popWithBound with
  | none => none
  | some (⟨b, e⟩, Q') => some (⟨b, bound (prio b) e⟩, Q')

/--
Assuming the elements in the estimator queue have non-decreasing bounds,
pop off the element with the lowest priority.
-/
def pop (Q : EstimatorQueue β prio ε) : Option (β × EstimatorQueue β prio ε) :=
  match Q.popWithBound with
  | none => none
  | some (⟨b, _⟩, Q') => some (b, Q')

partial def toListWithPriority (Q : EstimatorQueue β prio ε) : List (β × ℕ) :=
  match Q.popWithPriority with
  | none => []
  | some (p, Q) => p :: Q.toListWithPriority

partial def toList (Q : EstimatorQueue β prio ε) : List β :=
  match Q.pop with
  | none => []
  | some (b, Q) => b :: Q.toList
