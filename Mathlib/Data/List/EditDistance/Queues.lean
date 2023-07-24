/-
Copyright (c) 2023 Kim Liesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Liesinger
-/
import Mathlib.Data.List.EditDistance.Estimator
import Mathlib.Data.ListM.BestFirst

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

-- TODO proper implementation
partial def splitParentheses (s : String) : List String :=
  if s.startsWith "(" then
    "(" :: splitParentheses (s.drop 1)
  else if s.endsWith ")" then
    splitParentheses (s.dropRight 1) ++ [")"]
  else
    [s]

def tokenize (e : Expr) : MetaM (List String) := do
  let s := (← ppExpr e).pretty
  return s.toList.map (fun c => c.toString)
  -- return s.splitOn.map splitParentheses |>.join

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

namespace SearchNode

def mk (history : Array (Name × Bool)) (goal : MVarId) (ctx : Option MetavarContext := none) :
    MetaM SearchNode := do
  let type ← instantiateMVars (← goal.getType)
  match type.eq? with
  | none => failure
  | some (_, lhs, rhs) => pure <|
    { history := history
      mctx := ← ctx.getDM getMCtx
      goal := goal
      type := type
      ppGoal := (← ppExpr type).pretty
      lhs := ← tokenize lhs
      rhs := ← tokenize rhs }

def init (goal : MVarId) : MetaM SearchNode := mk #[] goal
def push (n : SearchNode) (name : Name) (symm : Bool) (g : MVarId) (ctx : Option MetavarContext := none) :=
  mk (n.history.push (name, symm)) g ctx

instance : Ord SearchNode where
  compare := compareOn SearchNode.ppGoal

abbrev prio (n : SearchNode) : Thunk Nat := Thunk.mk fun _ => (levenshtein Levenshtein.default n.lhs n.rhs)
abbrev estimator (n : SearchNode) : Type := LevenshteinEstimator Levenshtein.default n.lhs n.rhs

def rewrite (n : SearchNode) (r : Mathlib.Tactic.Rewrites.RewriteResult) : MetaM SearchNode :=
  withMCtx r.mctx do
    let goal' ← n.goal.replaceTargetEq r.result.eNew r.result.eqProof
    n.push r.name r.symm goal' (← getMCtx)

def rewrites (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)
    (n : SearchNode) : ListM MetaM SearchNode := .squash do
  IO.println <| "rewriting: " ++ n.ppGoal
  let results := Mathlib.Tactic.Rewrites.rewritesCore lemmas n.mctx n.goal n.type
  -- let results ← results.force
  -- let results := ListM.ofList results
  return results.mapM fun r => do
    n.rewrite r

def search (n : SearchNode) : ListM MetaM SearchNode := .squash do
  let lemmas ← Mathlib.Tactic.Rewrites.rewriteLemmas.get
  return bestFirstSearchCore SearchNode.prio SearchNode.estimator (rewrites lemmas) n

end SearchNode

open Lean Elab Tactic

elab "rewrite_search" : tactic => do
  let init ← SearchNode.init (← getMainGoal)
  let results := init.search
  let results := results.take 200
  for r in results do
    IO.println <| "steps: " ++ s!"{r.history}"
    IO.println <| "goal: " ++ r.ppGoal

-- set_option trace.Tactic.rewrites.lemmas true
-- set_option trace.Tactic.rewrites true

example (xs ys : List α) : (xs ++ ys).length = ys.length + xs.length := by
  rewrite_search


-- structure SearchState (σ : Type) where
--   s : σ
--   mctx : MetavarContext
--   goal : MVarId
--   ppGoal : String

-- def SearchState.init (s : σ) (goal : MVarId) : MetaM (SearchState σ) := do
--   pure <|
--   { s := s
--     mctx := ← getMCtx
--     goal := goal
--     ppGoal := (← ppExpr (← goal.getType)).pretty }

-- def SearchState.getType (state : SearchState σ) : MetaM Expr := withMCtx state.mctx do
--   instantiateMVars (← state.goal.getType)

-- -- def tokenizeGoal (state : SearchState σ) : MetaM (List String) := withMCtx state.mctx do
-- --   tokenize (← state.goal.getType)

-- -- @[reducible]
-- -- def GoalTargetQueue (target : SearchState σ) (tokens : List String) : Type :=
-- --   EditDistanceTargetQueue (fun p => p.1) (tokens, target)

-- -- def mkGoalQueue (data : SearchState σ) : MetaM (Σ tokens, GoalTargetQueue data tokens) := do
-- --   pure ⟨← tokenizeGoal data, ← Queue.empty⟩

-- def tokenizeEquality {σ : Type} (data : SearchState σ) : MetaM (List String × List String) :=
--   withMCtx data.mctx do
--     match (← data.goal.getType).eq? with
--     | some (_, lhs, rhs) =>
--       pure (← tokenize lhs, ← tokenize rhs)
--     | none => failure

-- @[reducible]
-- def EqualityQueue (σ β : Type) : Type :=
--   EditDistanceQueue (fun p : ((List String × List String) × SearchState σ) × β => p.1.1)

-- example : Queue MetaM (((List String × List String) × SearchState σ) × β) (EqualityQueue σ β) := inferInstance

-- def mkEqualityQueue : MetaM (EqualityQueue σ β) := Queue.empty

-- variable (lemmas : DiscrTree (Name × Bool × Nat) s × DiscrTree (Name × Bool × Nat) s)

-- def qux (s : SearchState (List (Name × Bool))) (r : Mathlib.Tactic.Rewrites.RewriteResult) : MetaM (SearchState (List (Name × Bool))) :=
--   withoutModifyingState do
--     withMCtx s.mctx do
--       let goal' ← s.goal.replaceTargetEq r.result.eNew r.result.eqProof
--       pure <|
--       { s := (r.name, r.symm) :: s.s
--         mctx := ← getMCtx
--         goal := goal'
--         ppGoal := (← ppExpr (← goal'.getType)).pretty }

-- def rewrites (state : (List String × List String) × SearchState (List (Name × Bool))) : ListM MetaM ((List String × List String) × SearchState (List (Name × Bool))) := .squash do
--   let foo := Mathlib.Tactic.Rewrites.rewritesCore lemmas state.2.goal (← state.2.getType)
--   return foo.mapM fun r => do
--     let s ← qux state.2 r
--     pure (← tokenizeEquality s, s)

-- -- We need this because `bestFirstSearchImpl` has an internal RBSet... blech.
-- instance : Ord ((List String × List String) × SearchState σ) where
--   compare s t := compare s.2.ppGoal t.2.ppGoal
