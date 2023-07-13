import Mathlib.Order.RelClasses
import Mathlib.Algebra.Order.Group.Defs

class Estimator (a : α) (ε : Type _) where
  bound : ε → α
  improve : ε → Option ε

class LawfulEstimator [Preorder α] (a : α) (ε : Type _) extends Estimator a ε where
  bound_le e : bound e ≤ a
  improve_spec e : match improve e with
    | none => bound e = a
    | some e' => bound e < bound e'

attribute [local instance] WellFoundedLT.toWellFoundedRelation

open LawfulEstimator

def Estimator.improveUntil (a : ℕ) (p : ℕ → Bool) [LawfulEstimator a ε] (e : ε) : Option ε :=
  if p (bound a e) then
    return e
  else
    match improve a e, improve_spec e with
    | none, _ => none
    | some e', lt =>
      have : a - bound a e' < a - bound a e :=
        Nat.sub_lt_sub_left (lt_of_lt_of_le lt (bound_le e')) lt
      Estimator.improveUntil a p e'
termination_by Estimator.improveUntil p I e => a - bound a e

theorem Estimator.improveUntil_spec
    (a : ℕ) (p : ℕ → Bool) [LawfulEstimator a ε] (e : ε) :
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
        Nat.sub_lt_sub_left (lt_of_lt_of_le lt (bound_le e')) lt
      exact Estimator.improveUntil_spec a p e'
termination_by Estimator.improveUntil_spec p I e => a - bound a e
