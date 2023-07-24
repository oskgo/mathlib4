/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.EditDistance.Estimator
import Mathlib.Data.ListM.BestFirst
import Mathlib.Order.Estimator.Queue

/--
Given `f : β → List α × List α`, this is a priority queue of `β`s which
always returns the element `b : β` such that the pair `f b` is as close as possible.
-/
@[reducible]
def EditDistanceQueue (f : β → List α × List α) [DecidableEq α] : Type _ := EstimatorQueue β
    (fun b => Thunk.mk fun _ => let ⟨xs, ys⟩ := f b; levenshtein Levenshtein.default xs ys)
    (fun b => let ⟨xs, ys⟩ := f b; LevenshteinEstimator Levenshtein.default xs ys)

set_option maxHeartbeats 2000 in
/-- info: [1, 4, 5] -/
#guard_msgs in
#eval (∅ : EditDistanceQueue id).pushAll
  [("hello".toList, "world".toList),
    ((" ... ".intercalate <| List.replicate 100 "nothing to see here").toList,
      (" ... ".intercalate <| List.replicate 100 "another long phrase").toList),
    ("cat".toList, "hat".toList)]
  |>.toListWithPriority.map (·.2)

/--
Given `f : β → List α` and a "target" `t : β`, this is a priority queue of `β`s which
always returns the element `b : β` such that `f b` is as close as possible to `f t`.
-/
@[reducible]
def EditDistanceTargetQueue (f : β → List α) [DecidableEq α] (t : β) : Type _ :=
  let xs := f t
  EstimatorQueue β
    (fun b => Thunk.mk fun _ => levenshtein Levenshtein.default xs (f b))
    (fun b => LevenshteinEstimator Levenshtein.default xs (f b))

set_option maxHeartbeats 2000 in
/-- info: [5, 13, 14] -/
#guard_msgs in
#eval (∅ : EditDistanceTargetQueue id "hello world".toList).pushAll
  [(" ... ".intercalate <| List.replicate 100 "nothing to see here").toList,
    "kitten sitting".toList, "yellow whirl".toList]
  |>.toListWithPriority.map (·.2)

open Lean Meta

partial def splitDelimiters (s : String) : List String :=
  if s.startsWith "(" || s.startsWith "[" then
    s.take 1 :: splitDelimiters (s.drop 1)
  else if s.endsWith ")" || s.endsWith "]" || s.endsWith "," then
    splitDelimiters (s.dropRight 1) ++ [s.takeRight 1]
  else
    [s]

def tokenize (e : Expr) : MetaM (List String) := do
  let s := (← ppExpr e).pretty
  -- return s.toList.map (fun c => c.toString)
  return s.splitOn.map splitDelimiters |>.join

open Qq in
#eval tokenize q(1 + (3 + 5))

-- @[reducible]
-- def EditDistanceExprTargetQueue (e : Expr) (tokens : List String) : Type :=
--   (EditDistanceTargetQueue (fun p => p.1) (tokens, e))

-- example (e : Expr) (tokens : List String) :
--     Queue MetaM (List String × Expr) (EditDistanceExprTargetQueue e tokens) :=
--   inferInstance

-- /--
-- Create a priority queue for `Expr`s which returns first whichever `Expr` is closest
-- (in edit distance, tokenizing at spaces and before and after parentheses)
-- to the specified `Expr`.
-- -/
-- def mkExprQueue (e : Expr) : MetaM (Σ tokens, EditDistanceExprTargetQueue e tokens) := do
--   pure ⟨← tokenize e, ← Queue.empty⟩

-- def push {tokens} (q : EditDistanceExprTargetQueue e tokens) (e : Expr) : MetaM (EditDistanceExprTargetQueue e tokens) := do
--   Queue.push q (← tokenize e, e)

-- open Qq
-- #eval ListM.force <| .squash do
--   let e := q(1 + (3 + 5))
--   let mut ⟨_, q⟩ ← mkExprQueue e
--   q ← push q q(9 + (7 + 5))
--   q ← push q q(1 + (3 + 7))
--   q ← push q q((1 + 3) + 5)
--   return Queue.toListM q |>.mapM fun (e : List String × Expr) => ppExpr e.2

structure SearchNode where mk' ::
  history : Array (Name × Bool)
  mctx : MetavarContext
  goal : MVarId
  type : Expr
  ppGoal : String
  lhs : List String
  rhs : List String
  rfl? : Option Bool := none
  dist? : Option Nat := none

namespace SearchNode

def mk (history : Array (Name × Bool)) (goal : MVarId) (ctx : Option MetavarContext := none) :
    MetaM (Option SearchNode) := do
  let type ← instantiateMVars (← goal.getType)
  match type.eq? with
  | none => return none
  | some (_, lhs, rhs) =>
    let lhsTokens ← tokenize lhs
    let rhsTokens ← tokenize rhs
    return some
      { history := history
        mctx := ← ctx.getDM getMCtx
        goal := goal
        type := type
        ppGoal := (← ppExpr type).pretty
        lhs := lhsTokens
        rhs := rhsTokens }

def compute_rfl? (n : SearchNode) : MetaM SearchNode := withMCtx n.mctx do
  if (← try? n.goal.rfl).isSome then
    pure { n with mctx := ← getMCtx, rfl? := some true }
  else
    pure { n with rfl? := some false }

def compute_dist? (n : SearchNode) : SearchNode :=
  { n with dist? := some (levenshtein Levenshtein.default n.lhs n.rhs) }

def init (goal : MVarId) : MetaM (Option SearchNode) := mk #[] goal
def push (n : SearchNode) (name : Name) (symm : Bool) (g : MVarId) (ctx : Option MetavarContext := none) : MetaM (Option SearchNode) :=
  mk (n.history.push (name, symm)) g ctx

instance : Ord SearchNode where
  compare := compareOn SearchNode.ppGoal

abbrev prio (n : SearchNode) : Thunk Nat := Thunk.mk fun _ => (levenshtein Levenshtein.default n.lhs n.rhs)
abbrev estimator (n : SearchNode) : Type := LevenshteinEstimator Levenshtein.default n.lhs n.rhs

def rewrite (n : SearchNode) (r : Mathlib.Tactic.Rewrites.RewriteResult) : MetaM (Option SearchNode) :=
  withMCtx r.mctx do
    let goal' ← n.goal.replaceTargetEq r.result.eNew r.result.eqProof
    n.push r.name r.symm goal' (← getMCtx)

def rewrites (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (n : SearchNode) : ListM MetaM SearchNode := .squash do
  -- IO.println <| "rewriting: " ++ n.ppGoal
  let results := Mathlib.Tactic.Rewrites.rewritesCore lemmas n.mctx n.goal n.type
  -- let results ← results.force
  -- let results := ListM.ofList results
  return results.filterMapM fun r => do
    n.rewrite r

def search (n : SearchNode) : ListM MetaM SearchNode := .squash do
  let lemmas ← Mathlib.Tactic.Rewrites.rewriteLemmas.get
  let search := bestFirstSearchCore SearchNode.prio SearchNode.estimator (rewrites lemmas) n
  let search := search.mapM SearchNode.compute_rfl?
  return search.takeUpToFirst fun n => n.rfl? = some true

end SearchNode

open Lean Elab Tactic

syntax "rewrite_search" : tactic

elab_rules : tactic |
    `(tactic| rewrite_search%$tk) => do
  let .some init ← SearchNode.init (← getMainGoal) | throwError "Goal is not an equality."
  let results := init.search
  let results := results.map fun r => r.compute_dist?
  let results := results.takeUpToFirst (fun r => r.dist? = some 0)
    |>.whileAtLeastHeartbeatsPercent 20
  let results ← results.force
  -- for r in results do
  --   IO.println <| "steps: " ++ s!"{r.history}"
  --   IO.println <| "goal: " ++ r.ppGoal
  let min ← match results with
  | [] => failure
  | h :: t => pure <| t.foldl (init := h) fun r₁ r₂ => if r₁.dist?.getD 0 ≤ r₂.dist?.getD 0 then r₁ else r₂
  -- IO.println <| "best: " ++ s!"{min.history}"
  setMCtx min.mctx
  replaceMainGoal [min.goal]
  let rules ← min.history.toList.mapM fun ⟨n, s⟩ => do pure (← mkConstWithFreshMVarLevels n, s)
  let type? := if min.rfl? = some true then none else some (← min.goal.getType)
  addRewritesSuggestion tk rules
    type? (origSpan? := ← getRef)

example (xs ys : List α) : (xs ++ ys).length = ys.length + xs.length := by
  rewrite_search

example [AddCommMonoid α] {a b c d : α} : (a + b) + (c + d) = a + d + c + b := by
  rewrite_search

example (xs ys : List α) :
    (xs ++ ys ++ ys).length = 2 * ys.length + xs.length := by
  rewrite_search
