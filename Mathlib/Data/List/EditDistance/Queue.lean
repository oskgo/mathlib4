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
