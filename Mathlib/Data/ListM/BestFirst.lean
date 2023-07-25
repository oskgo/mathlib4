/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic
import Mathlib.Order.Estimator
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Finset.Preimage

/-!
# Best first search

We perform best first search of a tree or graph,
where the neighbours of a vertex are provided by a lazy list `α → ListM m α`.

We maintain a priority queue of visited-but-not-exhausted nodes,
and at each step take the next child of the highest priority node in the queue.

This is useful in meta code for searching for solutions in the presence of alternatives.
It can be nice to represent the choices via a lazy list,
so the later choices don't need to be evaluated while we do depth first search on earlier choices.

Options:
* `maxDepth` allows bounding the search depth
* `maxQueued` implements "beam" search,
  by discarding elements from the priority queue when it grows too large
* `removeDuplicates` maintains an `RBSet` of previously visited nodes;
  otherwise if the graph is not a tree nodes may be visited multiple times.
-/

open Std EstimatorData Estimator Set

/-!
We begin by defining a best-first queue of `ListM`s.
This is a somewhat baroque data structure designed for the application in this file
(and in particularly for the implementation of `rewrite_search`).
If someone would like to generalize appropriately that would be great.

We want to maintain a priority queue of `ListM m β`, each indexed by some `a : α` with a priority.
To complicate matters, the priorities might be expensive to calculate,
so we instead keep track of a lower bound for each such `a : α`.
The priority queue maintains the `ListM m β` in order of the current best lower bound for the
corresponding `a : α`.
When we insert a new `α × ListM m β` into the queue, we have to provide a lower bound,
and we just insert it at a position depending on the estimate.
When it is time to pop a `β` off the queue, we iteratively improve the lower bound for the
front element of the queue, until we decide that either it must be the least element,
or we can exchange it with the second element of the queue and continue.

A `BestFirstQueue prio ε m β maxSize` consists of an `RBMap`,
where the keys are in `BestFirstNode prio ε`
and the values are `ListM m β`.

A `BestFirstNode prio ε` consists of a `key : α` and an estimator `ε : key`.
Here `ε` provides the current best lower bound for `prio key : Thunk ω`.
(The actual priority is hidden behind a `Thunk` to avoid evaluating it, in case it is expensive.)

We ask for the type classes `LinearOrder ω` and `∀ a : α, Estimator (prio a) (ε a)`.
This later typeclass ensures that we can always produce progressively better estimates
for a priority. We also need a `WellFounded` instance to ensure that improving estimates terminates.

This whole structure is designed around the problem of searching rewrite graphs,
prioritising according to edit distances (either between sides of an equation,
or from a goal to a target). Edit distance computations are particularly suited to this design
because the usual algorithm for computing them produces improving lower bounds at each step.

With this design, it is okay if we visit nodes with very large edit distances:
while these would be expensive to compute, we never actually finish the computation
except in cases where the node arrives at the front of the queue.
-/
section

/-- A node in a `BestFirstQueue. -/
structure BestFirstNode (prio : α → Thunk ω) (ε : α → Type) where
  key : α
  estimator : ε key

variable {α : Type} {prio : α → Thunk ω} {ε : α → Type} [LinearOrder ω]
  [∀ a, Estimator (prio a) (ε a)]
  [∀ a : α, WellFoundedGT (range (bound (prio a) : ε a → ω))]
  {m : Type → Type} [Monad m] {β : Type}

/-- Calculate the current best lower bound for the the priority of a node. -/
def BestFirstNode.estimate (n : BestFirstNode prio ε) : ω := bound (prio n.key) n.estimator

instance [Ord ω] [Ord α] : Ord (BestFirstNode prio ε) where
  compare :=
    compareLex
      (compareOn BestFirstNode.estimate)
      (compareOn BestFirstNode.key)

variable (prio ε m β) [Ord ω] [Ord α] in
set_option linter.unusedVariables false in
/-- A queue of `ListM m β`s, lazily prioritized by lower bounds. -/
def BestFirstQueue (maxSize : Option Nat) := RBMap (BestFirstNode prio ε) (ListM m β) compare

variable [Ord ω] [Ord α] {maxSize : Option Nat}

namespace BestFirstQueue

/--
Add a new `ListM m β` to the `BestFirstQueue`, and if this takes the size above `maxSize`,
eject a `ListM` from the tail of the queue.
-/
-- Note this ejects the element with the greatest estimated priority,
-- not necessarily the greatest priority!
def insertAndEject
    (q : BestFirstQueue prio ε m β maxSize) (n : BestFirstNode prio ε) (l : ListM m β) :
    BestFirstQueue prio ε m β maxSize :=
  match maxSize with
  | none => q.insert n l
  | some max =>
    if q.size < max then
      q.insert n l
    else
      match q.max with
      | none => RBMap.empty
      | some m => q.insert n l |>.erase m.1

/--
Pop a `β` off the `ListM m β` with lowest priority,
also returning the index in `α` and the current best lower bound for its priority.
This may require improving estimates of priorities and shuffling the queue.
-/
partial def popWithBound (q : BestFirstQueue prio ε m β maxSize) :
    m (Option (((a : α) × (ε a) × β) × BestFirstQueue prio ε m β maxSize)) := do
  let s := @toStream (RBMap _ _ _) _ _ q
  match s.next? with
  | none => pure none
  | some ((n, l), s') => match s'.next? with
    | none => do match ← l.uncons with
      | none => pure none
      | some (b, l') => pure <| some (⟨n.key, n.estimator, b⟩, RBMap.single n l')
    | some ((m, _), _) =>
      match improveUntil (prio n.key) (m.estimate < ·) n.estimator with
      | .error e => do match ← l.uncons with
        | none => popWithBound (q.erase n)
        | some (b, l') =>
          match e with
          | none => pure <| some (⟨n.key, n.estimator, b⟩, q.modify n fun _ => l')
          | some e' => pure <| some (⟨n.key, e', b⟩, q.erase n |>.insert ⟨n.key, e'⟩ l')
      | .ok e' => popWithBound (q.erase n |>.insert ⟨n.key, e'⟩ l)

/--
Pop a `β` off the `ListM m β` with lowest priority,
also returning the index in `α` and the value of the current best lower bound for its priority.
-/
def popWithPriority (q : BestFirstQueue prio ε m β maxSize) :
    m (Option (((α × ω) × β) × BestFirstQueue prio ε m β maxSize)) := do
  match ← q.popWithBound with
  | none => pure none
  | some (⟨a, e, b⟩, q') => pure (some (((a, bound (prio a) e), b), q'))

/--
Pop a `β` off the `ListM m β` with lowest priority.
-/
def pop (q : BestFirstQueue prio ε m β maxSize) :
    m (Option ((α × β) × BestFirstQueue prio ε m β maxSize)) := do
  match ← q.popWithBound with
  | none => pure none
  | some (⟨a, _, b⟩, q') => pure (some ((a, b), q'))

/--
Convert a `BestFirstQueue` to a `ListM ((α × ω) × β)`, by popping off all elements,
recording also the values in `ω` of the best current lower bounds.
-/
-- This is not used in the algorithms below, but can be useful for debugging.
partial def toListMWithPriority (q : BestFirstQueue prio ε m β maxSize) : ListM m ((α × ω) × β) :=
  .squash do
    match ← q.popWithPriority with
    | none => pure .nil
    | some (p, q') => pure <| ListM.cons' p q'.toListMWithPriority

/--
Convert a `BestFirstQueue` to a `ListM (α × β)`, by popping off all elements.
-/
def toListM (q : BestFirstQueue prio ε m β maxSize) : ListM m (α × β) :=
  q.toListMWithPriority.map fun t => (t.1.1, t.2)

end BestFirstQueue

open ListM

variable {m : Type → Type} [Monad m] [Alternative m] [∀ a, Bot (ε a)] (prio ε)

/--
Core implementation of `bestFirstSearch`, that works by iteratively updating an internal state,
consisting of a priority queue of `ListM m α`.

At each step we pop an element off the queue,
compute its children (lazily) and put these back on the queue.
-/
def impl (maxSize : Option Nat) (f : α → ListM m α) (a : α) : ListM m α :=
  let init : BestFirstQueue prio ε m α maxSize := RBMap.single ⟨a, ⊥⟩ (f a)
  cons do pure (some a, iterate go |>.runState' init)
where go : StateT (BestFirstQueue prio ε m α maxSize) m α := fun s => do
  match ← s.pop with
    | none => failure
    | some ((_, b), s') => pure (b, s'.insertAndEject ⟨b, ⊥⟩ (f b))

/--
Wrapper for `impl` implementing the `maxDepth` option.
-/
def implMaxDepth (maxSize : Option Nat) (maxDepth : Option Nat) (f : α → ListM m α) (a : α) :
    ListM m α :=
  match maxDepth with
  | none => impl prio ε maxSize f a
  | some max =>
    let f' : α ×ₗ Nat → ListM m (α × Nat) := fun ⟨a, n⟩ =>
      if max < n then
        nil
      else
        (f a).map fun a' => (a', n + 1)
    impl (fun p : α ×ₗ Nat => prio p.1) (fun p : α ×ₗ Nat => ε p.1) maxSize f' (a, 0) |>.map (·.1)

/--
A lazy list recording the best first search of a graph generated by a function
`f : α → ListM m α`.

We maintain a priority queue of visited-but-not-exhausted nodes,
and at each step take the next child of the highest priority node in the queue.

The option `maxDepth` limits the search depth.

The option `maxQueued` bounds the size of the priority queue,
discarding the lowest priority nodes as needed.
This implements a "beam" search, which may be incomplete but uses bounded memory.

The option `removeDuplicates` keeps an `RBSet` of previously visited nodes.
Otherwise, if the graph is not a tree then nodes will be visited multiple times.

This version allows specifying a custom priority function `prio : α → Thunk ω`
along with estimators `ε : α → Type` equipped with `[∀ a, Estimator (prio a) (ε a)]`
that control the behaviour of the priority queue.
This function returns values `a : α` that have
the lowest possible `prio a` amongst unvisited neighbours of visited nodes,
but lazily estimates these priorities to avoid unnecessary computations.
-/
def bestFirstSearchCore (f : α → ListM m α) (a : α)
    (maxQueued : Option Nat := none) (maxDepth : Option Nat := none) (removeDuplicates := true) :
    ListM m α :=
  if removeDuplicates then
    let f' : α → ListM (StateT (RBSet α compare) m) α := fun a =>
      (f a).liftM >>= fun b => do
        guard !(← get).contains b
        modify fun s => s.insert b
        pure b
    implMaxDepth prio ε maxQueued maxDepth f' a |>.runState' (RBSet.empty.insert a)
  else
    implMaxDepth prio ε maxQueued maxDepth f a

end

variable [Monad m] [Alternative m] [LinearOrder α]

/--
A lazy list recording the best first search of a graph generated by a function
`f : α → ListM m α`.

We maintain a priority queue of visited-but-not-exhausted nodes,
and at each step take the next child of the highest priority node in the queue.

The option `maxDepth` limits the search depth.

The option `maxQueued` bounds the size of the priority queue,
discarding the lowest priority nodes as needed.
This implements a "beam" search, which may be incomplete but uses bounded memory.

The option `removeDuplicates` keeps an `RBSet` of previously visited nodes.
Otherwise, if the graph is not a tree then nodes will be visited multiple times.

This function returns values `a : α` that are least in the `[LinearOrder α]`
amongst unvisited neighbours of visited nodes.
-/
-- Although the core implementation lazily computes estimates of priorities,
-- this version does not take advantage of those features.
def bestFirstSearch (f : α → ListM m α) (a : α)
    (maxQueued : Option Nat := none) (maxDepth : Option Nat := none) (removeDuplicates := true) :
    ListM m α :=
  bestFirstSearchCore Thunk.pure (fun a : α => { x // x = a }) f a
    maxQueued maxDepth removeDuplicates
