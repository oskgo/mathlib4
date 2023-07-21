/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic

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

open Std

/--
View a type `Q` as a monadic priority queue of `α`.

We can push an element on to the queue or pop an element off.
No guarantees about the order is implied
(or indeed any relation between pushed and popped elements).
-/
-- If this proves useful elsewhere it can be moved up the import hierarchy.
class Queue (m : Type u → Type u) (α : outParam (Type u)) (Q : Type u) where
  empty : m Q
  push : Q → α → m Q
  pop : Q → m (Option (α × Q))

instance [Monad m] [MonadLift m n] [Queue m α Q] : Queue n α Q where
  empty := (Queue.empty : m Q)
  push q a := (Queue.push q a : m Q)
  pop q := (Queue.pop q : m _)

instance [Monad m] (α : Type _) : Queue m α (List α) where
  empty := pure []
  push Q a := pure (a :: Q)
  pop := fun
  | [] => pure none
  | h :: t => pure (some (h, t))

def Queue.pushAll [Monad m] [Queue m α Q] (q : Q) (l : List α) : m Q :=
  l.foldlM (init := q) fun q' a => Queue.push q' a

/-- Read a queue as a lazy list. -/
partial def Queue.toListM [Monad m] [Queue m α Q] (q : Q) : ListM m α :=
  .squash do
    match ← Queue.pop q with
    | none => pure .nil
    | some (a, q') => pure <| ListM.cons' a (Queue.toListM q')

def Queue.toList [Monad m] [Queue m α Q] (q : Q) : m (List α) :=
  ListM.force (Queue.toListM q)

-- set_option linter.unusedVariables false in
-- /--
-- If we can view a type `Q` as a monadic priority queue of `α × β`,
-- and we have a monadic function `f : β → m α`
-- that can "reconstruct" the second elements of such pairs,
-- then this wrapper can be viewed as a monadic priority queue of `β`.

-- (The "reconstructable" value comes first in the pair because we'll often be sorting by it.)
-- -/
-- def Queue.snd {m : Type _ → Type _} (f : α → m β) (Q : Type _) : Type := Q

-- instance [Monad m] {α β} {f : β → m α} [Queue m (α × β) Q] : Queue m β (Queue.snd f Q) where
--   empty := (Queue.empty : m Q)
--   push q b := do (Queue.push q (← f b, b) : m Q)
--   pop (q : Q) := do
--     match ← Queue.pop q with
--     | none => pure none
--     | some ((_, b), q) => pure (some (b, q))

/--
View an `RBMap α β compare` as a `Queue` of `α × β`,
popping pairs with the least `α` component first.
If `bound = some n`, then when pushing a pair would cause the length of the queue to exceed `n`,
the pair with largest `α` component is discarded.

Note that enqueuing multiple elements with the same first component will discard the earlier ones.
-/
def rbMapQueue (m : Type u → Type u) [Monad m] (α β : Type u) [Ord α] (bound : Option Nat := none) :
    Queue m (α × β) (RBMap α β compare) where
  empty := pure ∅
  push Q := fun ⟨a, b⟩ =>
    let R := Q.insert a b
    match bound with
    | none => pure R
    | some b => if R.size ≤ b then pure R else match R.max with
      | none => unreachable!
      | some (a', _) => pure (R.erase a')
  pop Q := match Q.min with
  | none => pure none
  | some (a, b) => pure (some ((a, b), Q.erase a))

variable {α : Type u} {m : Type u → Type u} [Monad m] [Alternative m]

open ListM Queue

/--
Auxiliary function for `bestFirstSearch`, that updates the internal state,
consisting of a priority queue of triples `α × Nat × ListM m α`.
We remove the next element from the list contained in the best triple
(discarding the triple if there is no next element),
enqueue it and return it.
-/
-- The return type has `× List α` rather than just `× Option α` so `bestFirstSearch` can use `fixl`.
-- The list has length at most one.
def bestFirstSearchAux [Queue m (α × (Nat × ListM m α)) Q]
    (f : Nat → α → ListM m α) (s : Q) : m (Q × List α) := do
  match ← Queue.pop s with
  | none => failure
  | some ((a, (n, L)), s') =>
    match ← uncons L with
    | none => pure (s', [])
    | some (b, L') => do
      let s' ← Queue.push (← Queue.push s' (a, (n, L'))) (b, (n + 1, f (n+1) b))
      pure (s', [b])

variable [Ord α]

/--
Implementation of the `bestFirstSearch` function,
allowing for an arbitrary `Queue` data structure which handles prioritization.
-/
def bestFirstSearchImpl (Q : Type u → Type u) [∀ β : Type u, Queue m (α × β) (Q β)]
    (f : α → ListM m α) (a : α)
    (maxDepth : Option Nat := none) (removeDuplicates := true) :
    ListM m α := squash do
  let f := match maxDepth with
  | none => fun _ a => f a
  | some d => fun n a => if d < n then empty else f a
  if removeDuplicates then
    let f' : Nat → α → ListM (StateT.{u} (RBSet α compare) m) α := fun n a =>
      (f n a).liftM >>= fun b => do
        let s ← get
        if s.contains b then failure
        set <| s.insert b
        pure b
    let init ← Queue.push (← Queue.empty : Q (Nat × _)) (a, (0, f' 0 a))
    return cons (do pure (some a, fixl (bestFirstSearchAux f') init))
      |>.runState' (RBSet.empty.insert a)
  else
    let init ← Queue.push (← Queue.empty : Q (Nat × _)) (a, (0, f 0 a))
    return cons do pure (some a, fixl (bestFirstSearchAux f) init)

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
-/
def bestFirstSearch (f : α → ListM m α) (a : α)
    (maxDepth : Option Nat := none) (maxQueued : Option Nat := none) (removeDuplicates := true) :
    ListM m α :=
  have := fun (β : Type u) => rbMapQueue m α β maxQueued
  bestFirstSearchImpl (fun β => RBMap α β compare) f a maxDepth removeDuplicates
