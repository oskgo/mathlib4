/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.ListM.Basic
import Mathlib.Order.Estimator
import Mathlib.Data.Prod.Lex

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

open EstimatorData Estimator Set

section

structure BestFirstNode (prio : α → Thunk ω) (ε : α → Type) where
  key : α
  estimator : ε key

variable {α : Type} {prio : α → Thunk ω} {ε : α → Type} [LinearOrder ω]
  [∀ a, Estimator (prio a) (ε a)]
  [∀ a : α, WellFoundedGT (range (bound (prio a) : ε a → ω))]
  {m : Type → Type} [Monad m] {β : Type}

def BestFirstNode.estimate (n : BestFirstNode prio ε) : ω := bound (prio n.key) n.estimator

instance [Ord ω] [Ord α] : Ord (BestFirstNode prio ε) where
  compare :=
    compareLex
      (compareOn BestFirstNode.estimate)
      (compareOn BestFirstNode.key)

variable (prio ε m β) [Ord ω] [Ord α] in
set_option linter.unusedVariables false in
def BestFirstQueue (maxSize : Option Nat) := RBMap (BestFirstNode prio ε) (ListM m β) compare

variable [Ord ω] [Ord α] {maxSize : Option Nat}
variable [ToString ω]

def printPriorities (q : BestFirstQueue prio ε m β maxSize) (f : Unit → θ) : θ :=
  let keys := RBMap.toList q |>.map (·.1.key)
  let priorities := keys.map (fun a => (prio a).get)
  let bounds := RBMap.toList q |>.map (fun a => (⟨a.1.key, a.1.estimator⟩ : Σ (a : α), ε a)) |>.map (fun p => bound (prio p.1) p.2)
  dbgTrace (toString priorities ++ "\n" ++ toString bounds) f


namespace BestFirstQueue

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

-- def pushNode (q : BestFirstQueue prio ε m β) (n : BestFirstNode prio ε m β) :
--     BestFirstQueue prio ε m β :=
--   match q with
--   | [] => [n]
--   | h :: (t : BestFirstQueue prio ε m β) =>
--     if n.estimate ≤ h.estimate then
--       n :: h :: t
--     else
--       h :: t.pushNode n

-- partial def popWithBound (q : BestFirstQueue prio ε m β) :
--     m (Option ((β × (a : α) × (ε a)) × BestFirstQueue prio ε m β)) :=
--   match q with
--   | [] => pure none
--   | [x] => do match ← x.value.uncons with
--     | none => pure none
--     | some (b, v') => pure <| some ((b, ⟨x.key, x.estimator⟩), [{ x with value := v' }])
--   | x :: y :: (t : BestFirstQueue prio ε m β) =>
--     match improveUntil (prio x.key) (y.estimate < ·) x.estimator with
--     | .error e => do match ← x.value.uncons with
--       | none => popWithBound (y :: t)
--       | some (b, v') =>
--         let e' := e.getD x.estimator
--         pure <| some ((b, ⟨x.key, e'⟩), { x with estimator := e', value := v' } :: y :: t)
--     | .ok e₁' => popWithBound (y :: t.pushNode { x with estimator := e₁' })

def popWithPriority (q : BestFirstQueue prio ε m β maxSize) :
    m (Option (((α × β) × ω) × BestFirstQueue prio ε m β maxSize)) := do
  match ← q.popWithBound with
  | none => pure none
  | some (⟨a, e, b⟩, q') => pure (some (((a, b), bound (prio a) e), q'))

def pop (q : BestFirstQueue prio ε m β maxSize) : m (Option ((α × β) × BestFirstQueue prio ε m β maxSize)) := do
  match ← (printPriorities q (fun _ => q)).popWithBound with
  | none => pure none
  | some (⟨a, _, b⟩, q') => pure (some ((a, b), q'))

partial def toListMWithPriority (q : BestFirstQueue prio ε m β maxSize) : ListM m ((α × β) × ω) := .squash do
  match ← q.popWithPriority with
  | none => pure .nil
  | some (p, q') => pure <| ListM.cons' p q'.toListMWithPriority

def toListM (q : BestFirstQueue prio ε m β maxSize) : ListM m (α × β) :=
  q.toListMWithPriority.map (·.1)

end BestFirstQueue

variable {m : Type → Type} [Monad m] [Alternative m]

open ListM Queue

variable [∀ a, Bot (ε a)]

variable (prio ε)

/--
Auxiliary function for `bestFirstSearch`, that updates the internal state,
consisting of a priority queue of triples `α × Nat × ListM m α`.
We remove the next element from the list contained in the best triple
(discarding the triple if there is no next element),
enqueue it and return it.
-/
def bestFirstSearchAux
    (f : α → ListM m α) : StateT (BestFirstQueue prio ε m α maxSize) m α := fun s => do
    match ← s.pop with
    | none => failure
    | some ((_, b), s') => pure (b, s'.insertAndEject ⟨b, ⊥⟩ (f b))

def impl (maxSize : Option Nat) (f : α → ListM m α) (a : α) : ListM m α :=
  let init : BestFirstQueue prio ε m α maxSize := RBMap.single ⟨a, ⊥⟩ (f a)
  cons do pure (some a, iterate (bestFirstSearchAux prio ε f) |>.runState' init)

instance [Ord α] [Ord β] : Ord (α ×ₗ β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

def implMaxDepth (maxSize : Option Nat) (maxDepth : Option Nat) (f : α → ListM m α) (a : α) : ListM m α :=
  match maxDepth with
  | none => impl prio ε maxSize f a
  | some max =>
    let f' : α ×ₗ Nat → ListM m (α × Nat) := fun ⟨a, n⟩ => if max < n then empty else (f a).map fun a' => (a', n + 1)
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

@[simp] lemma le_of_subsingleton [Preorder α] [Subsingleton α] (a b : α) : a ≤ b ↔ True := by
  cases Subsingleton.elim a b
  simp

@[simp] lemma not_lt_of_subsingleton [Preorder α] [Subsingleton α] (a b : α) : a < b ↔ False := by
  cases Subsingleton.elim a b
  simp


instance [Preorder α] [Unique α] : OrderBot α where
  bot := default
  bot_le a := by aesop

instance [Preorder α] [Unique α] : OrderTop α where
  top := default
  le_top a := by aesop

instance [Preorder α] [Unique α] : LocallyFiniteOrder α where
  finsetIcc _ _ := {default}
  finsetIoc _ _ := ∅
  finsetIco _ _ := ∅
  finsetIoo _ _ := ∅
  finset_mem_Icc := by aesop
  finset_mem_Ioc := by aesop
  finset_mem_Ico := by aesop
  finset_mem_Ioo := by aesop

instance [Preorder α] [Unique α] : LocallyFiniteOrderBot α where
  finsetIio _ := ∅
  finsetIic _ := {default}
  finset_mem_Iio := by aesop
  finset_mem_Iic := by aesop

instance [Preorder α] [Unique α] : LocallyFiniteOrderTop α where
  finsetIoi _ := ∅
  finsetIci _ := {default}
  finset_mem_Ioi := by aesop
  finset_mem_Ici := by aesop

variable [Monad m] [Alternative m] [LinearOrder α]

variable [ToString α] -- FIXME remove

def bestFirstSearch (f : α → ListM m α) (a : α)
    (maxQueued : Option Nat := none) (maxDepth : Option Nat := none) (removeDuplicates := true) :
    ListM m α :=
  bestFirstSearchCore Thunk.pure (fun a : α => { x // x = a }) f a
    maxQueued maxDepth removeDuplicates
