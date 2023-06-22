/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions

/-!

# `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `natDegree f ≤ d` or `degree f ≤ d`,
tries to solve the goal.  It may leave side-goals, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with equalities, instead of inequalities (i.e. implement `compute_degree`).
* Add functionality to deal with (some) exponents that are not closed natural numbers.
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree` and `natDegree` are equally supported.

##  Implementation details

We start with a goal of the form `natDegree f ≤ d` or `degree f ≤ d`.
Recurse into `f` breaking apart sums, products and powers.  Take care of numerals,
`C a, X (^ n), monomial a n` separately.
-/

section Tactic

namespace Mathlib.Tactic.ComputeDegree

open Lean Meta Elab.Tactic Polynomial

/-- Return `max a b` using `Max.max`. This method assumes `a` and `b` have the same type. -/
def mkMax (a b : Expr) : MetaM Expr := mkAppM ``Max.max #[a, b]

/-- Return `a ^ b` using `HPow.hPow`. -/
def mkPow (a b : Expr) : MetaM Expr := mkAppM ``HPow.hPow #[a, b]

/-- `toNatDegree alt pol` takes a function `alt : Expr → MetaM Expr` and `pol : Expr` as inputs.
It assumes that `pol` represents a polynomial and guesses an `Expr` for its `natDegree`.
It errs on the side of assuming that there are no zeros, e.g. `natDegree X = 1`,
regardless of whether the base-ring is `nontrivial` or not.
Everything that is not obtained as an iterated sum, product or `Nat`-power of `C`onstants, `Nat`s,
`X`s, `monomials` gets its guess to the `natDegree` outsourced to the function `alt`.

Chances are that `alt` is the constant function that, for an expression `f`, guesses the
`Expr`ession representing `natDegree f`.
-/
partial
def toNatDegree (alt : Expr → MetaM Expr) (pol : Expr) : MetaM Expr :=
match pol.getAppFnArgs with
  --  we assign a `natDegree` to the `Nat`s, the `C`onstants and `X`
  | (``OfNat.ofNat, _) => return mkNatLit 0
  | (``Nat.cast, _) => return mkNatLit 0
  | (``Int.cast, _) => return mkNatLit 0
  | (``Polynomial.X, _) => return mkNatLit 1
  --  we assign a `natDegree` to the powers: `natDegree (a ^ b) = b * natDegree a`
  --  with special support for `b ∈ {0, 1}`
  | (``Neg.neg, #[_, _, a]) => do
    toNatDegree alt a
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, a, b]) => do
    mkMul b (← toNatDegree alt a)
  --  we assign a `natDegree` to a `mul`: `natDegree (a * b) = natDegree a + natDegree b`
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
    mkAdd (← toNatDegree alt a) (← toNatDegree alt b)
  --  we assign a `natDegree` to an `add`: `natDegree (a + b) = max (natDegree a) (natDegree b)`
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
    mkMax (← toNatDegree alt a) (← toNatDegree alt b)
  --  we assign a `natDegree` to a `sub`: `natDegree (a - b) = max (natDegree a) (natDegree b)`
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
    mkMax (← toNatDegree alt a) (← toNatDegree alt b)
  --  we assign a `natDegree` to an `↑(monomial n) _`: `natDegree (↑(monomial n) _) = n`
  --  falling back to `alt pol`, if the `FunLike.coe` was not a `monomial`.
  | (``FunLike.coe, #[_, _, _, _, n, _]) =>
    match n.getAppFnArgs with
      | (``monomial, #[_, _, n]) => return n
      | (``C, _) => return mkNatLit 0
      | _ => alt pol
  --  everything else falls back to `alt pol`.
  | (_name, _args) => alt pol

def isDegLE (e : Expr) : CoreM (Bool × Expr × Expr) := do
  match e.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``degree, #[_, _, pol])    => return (false, pol, rhs)
      | (``natDegree, #[_, _, pol]) => return (true, pol, rhs)
      | (na, _) => throwError (f!"Expected an inequality of the form\n\n" ++
        f!"  'f.natDegree ≤ d'  or  'f.degree ≤ d',\n\ninstead, {na} appears on the LHS")
    | _ => throwError m!"Expected an inequality instead of '{e.getAppFnArgs.1}'"

def mkNatDegreeLE (f : Expr) : MetaM Expr := do
  let guessDegree := ← toNatDegree (fun p => dbg_trace p.getAppFnArgs; mkAppM ``natDegree #[p] <|> return mkNatLit 0) f
  let ndf := ← mkAppM ``natDegree #[f]
  let ndfLE := ← mkAppM ``LE.le #[ndf, guessDegree]
  pure ndfLE

partial
def CDL1 (pol : Expr) : TacticM Unit := do
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
let newPols := ← do match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
--    let lis := ← (← getMainGoal).apply (← mkAppM `Polynomial.natDegree_add_le #[f, g])
--    setGoals lis
    let fStx := ← f.toSyntax
    let gStx := ← g.toSyntax
    evalTactic (← `(tactic| refine (natDegree_add_le $fStx $gStx).trans ?_))
    evalTactic (← `(tactic| refine max_le_max ?_ ?_))
    pure [f, g]
  | (``Neg.neg, #[_, _, f])  =>
    let fStx := ← f.toSyntax
    evalTactic (← `(tactic| refine (natDegree_neg $fStx).le.trans ?_))
    pure [f]
  | (``HSub.hSub, #[_, _, _, _, f, g])  =>
    let fStx := ← f.toSyntax
    let gStx := ← g.toSyntax
    evalTactic (← `(tactic| refine (natDegree_sub_le $fStx $gStx).trans ?_))
    evalTactic (← `(tactic| refine max_le_max ?_ ?_))
    pure [f, g]
  | (``HMul.hMul, #[_, _, _, _, f, g])  =>
    evalTactic (← `(tactic| refine natDegree_mul_le.trans ?_))
    evalTactic (← `(tactic| refine add_le_add ?_ ?_))
    pure [f, g]
  -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
    let cStx := ← c.toSyntax
    if polFun.isAppOf ``Polynomial.C then
      evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
      pure []
    else if polFun.isAppOf ``Polynomial.monomial then
      evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
      pure []
    else throwError m!"'compute_degree_le' is not implemented for {polFun}"
  | (``Polynomial.X, _)  =>
    evalTactic (← `(tactic| exact natDegree_X_le))
    pure []
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => do
    evalTactic (← `(tactic| refine natDegree_pow_le.trans ?_))
    evalTactic (← `(tactic| refine Nat.mul_le_mul rfl.le ?_))
    pure [f]
  -- deal with `natDegree (n : Nat)`
  | (``Nat.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  -- deal with `natDegree (n : Int)`
  | (``Int.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_int_cast $nStx).le))
    pure []
  -- deal with `natDegree 0, 1, (n : Nat)`.
  -- I am not sure why I had to split `n = 0, 1, generic`.
  | (``OfNat.ofNat, #[_, n, _]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
      evalTactic (← `(tactic| exact natDegree_one.le)) <|>
      evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"
let _ := ← newPols.mapM fun x => focus (CDL1 x)

example (a : Int) (b : Nat) (hb : b ≤ 2) : natDegree (((3 * a : Int) : Int[X]) + ((X + C a * X + monomial 3 9) * X ^ b) ^ 2) ≤ 10 := by
  run_tac do
    let g ← getMainTarget
    let (is_natDeg, pol, d) := ← isDegLE g
--    logInfo m!"{(is_natDeg, pol, d)}"
    let nEQ := ← mkNatDegreeLE pol
--    logInfo m!"{nEQ}"
--    let mv := ← mkFreshMVarId
--    let sideGoal := ← mkFreshMVarId
    let _ := ← instantiateMVars nEQ
    let nEQS := ← nEQ.toSyntax
--    let nam := ← mkFreshUserName `myEq
    let ns : TSyntax `Mathlib.Tactic.optBinderIdent := { raw := mkAtom "" }
    let dcls := (←getLCtx).decls
--    dbg_trace dcls.toList.reduceOption.map (LocalDecl.userName ·)
    let (mv1, mv2) := ← haveLetCore (← getMainGoal) ns #[] (some nEQS) true
    setGoals [mv1]
    --evalTactic (← `(tactic| have : $nEQS))
    focusAndDone <| CDL1 pol
    setGoals [mv2]
    withMainContext do
    let dcls1 := (←getLCtx).decls
--    dbg_trace dcls.toList.reduceOption.map (LocalDecl.userName ·)
--    dbg_trace dcls1.toList.reduceOption.map (LocalDecl.userName ·)
--    dbg_trace dcls.size
--    dbg_trace dcls1.size
    let d := dcls1.toList.reduceOption.find? fun x =>
      ! ((dcls.toList.reduceOption.map (LocalDecl.toExpr ·)).contains x.toExpr)
    dbg_trace d.get!.userName
    let guessDegree := ← toNatDegree (fun p => dbg_trace p.getAppFnArgs; mkAppM ``natDegree #[p] <|> return mkNatLit 0) pol
    let gds := ← guessDegree.toSyntax
    let _ := ← evalTactic (← `(tactic| refine LE.le.trans (b := $gds) ?_ ?_))
    (← getMainGoal).assumption
    let newGoal := ← (← getMainGoal).clear d.get!.fvarId
    setGoals [newGoal]

    --let gs := ← mv2.apply d.get!.toExpr

--    let lem := ← mkAppM ``LE.le.trans #[d.get!.toExpr]
--    let _ := ← refineCore (← lem.toSyntax) `ciao true
--    dbg_trace dcls1.size == dcls.size
--    let hyp := ← getFVarLocalDecl nEQ
--    dbg_trace f!"{hyp.type}"
  --assumption
  --refine this.trans ?_
  --clear this
  --linarith [hb]
  show _ ≤ 2 * (3 + 2)
  simp
  assumption
  --mono
  --norm_num [hb]
#check assumption

section mylemmas

variable {R : Type _}

section semiring
variable [Semiring R]

theorem add {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f + g) ≤ max a b :=
(f.natDegree_add_le g).trans $ max_le_max ‹_› ‹_›

theorem mul {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f * g) ≤ a + b :=
(f.natDegree_mul_le).trans $ add_le_add ‹_› ‹_›

theorem pow {a b : Nat} {f : R[X]} (hf : natDegree f ≤ a) :
    natDegree (f ^ b) ≤ b * a :=
natDegree_pow_le.trans (Nat.mul_le_mul rfl.le ‹_›)

end semiring

section ring
variable [Ring R]

theorem neg {a : Nat} {f : R[X]} (hf : natDegree f ≤ a) : natDegree (- f) ≤ a :=
(natDegree_neg f).le.trans ‹_›

theorem sub {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f - g) ≤ max a b :=
(f.natDegree_sub_le g).trans $ max_le_max ‹_› ‹_›

end ring

end mylemmas

partial
def CDL (pol : Expr) : TacticM Unit := do
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
let newPols := ← do match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
    evalTactic (← `(tactic| refine add ?_ ?_))
    pure [f, g]
  | (``Neg.neg, #[_, _, f])  =>
    evalTactic (← `(tactic| refine neg ?_))
    pure [f]
  | (``HSub.hSub, #[_, _, _, _, f, g])  =>
    evalTactic (← `(tactic| refine sub ?_ ?_))
    pure [f, g]
  | (``HMul.hMul, #[_, _, _, _, f, g])  =>
    evalTactic (← `(tactic| refine mul ?_ ?_))
    pure [f, g]
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => do
    evalTactic (← `(tactic| refine pow ?_))
    pure [f]
  -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
    let cStx := ← c.toSyntax
    if polFun.isAppOf ``Polynomial.C then
      evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
    else if polFun.isAppOf ``Polynomial.monomial then
      evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
    else throwError m!"'compute_degree_le' is not implemented for {polFun}"
    pure []
  | (``Polynomial.X, _)  =>
    evalTactic (← `(tactic| exact natDegree_X_le))
    pure []
  -- deal with `natDegree (n : Nat)`
  | (``Nat.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  -- deal with `natDegree (n : Int)`
  | (``Int.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_int_cast $nStx).le))
    pure []
  -- deal with `natDegree 0, 1, (n : Nat)`.
  -- I am not sure why I had to split `n = 0, 1, generic`.
  | (``OfNat.ofNat, #[_, n, _]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
      evalTactic (← `(tactic| exact natDegree_one.le)) <|>
      evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"
let _ := ← newPols.mapM fun x => focus (CDL1 x)

def addNatDegreeDecl (stx : TSyntax `Mathlib.Tactic.optBinderIdent) (pol : Expr) : TacticM Unit :=
focus do
  let nEQ := ← mkNatDegreeLE pol
  let nEQS := ← nEQ.toSyntax
--  let ns : TSyntax `Mathlib.Tactic.optBinderIdent := { raw := mkAtom "" }
  let (mv1, mv2) := ← haveLetCore (← getMainGoal) stx #[] (some nEQS) true
  setGoals [mv1, mv2]
  focusAndDone $ CDL pol


theorem what : degree (((X : Int[X]) + (- X)) ^ 2 - monomial 5 8 * X ^ 4 * X + C 5 - 7 + (-10)) ≤ 10 := by
  run_tac do
    let g ← getMainTarget
    let (is_natDeg, pol, d) := ← isDegLE g
--    logInfo m!"{(is_natDeg, pol, d)}"
--    let nEQ := ← mkNatDegreeLE pol
--    logInfo m!"{nEQ}"
--    let mv := ← mkFreshMVarId
--    let sideGoal := ← mkFreshMVarId
--    let _ := ← instantiateMVars nEQ
--    let nEQS := ← nEQ.toSyntax
--    let nam := ← mkFreshUserName `myEq
--    let ns : TSyntax `Mathlib.Tactic.optBinderIdent := { raw := mkAtom "" }
    let dcls := (←getLCtx).decls
    addNatDegreeDecl { raw := mkAtom "oy" } pol
--    dbg_trace dcls.toList.reduceOption.map (LocalDecl.userName ·)
--    let (mv1, mv2) := ← haveLetCore (← getMainGoal) ns #[] (some nEQS) true
--    setGoals [mv1, mv2]
--    focusAndDone $ CDL pol
    --evalTactic (← `(tactic| have : $nEQS))
    --let (_, mvs) := (← CDL mv1 pol).unzip
--    setGoals (mvs ++ [mv2])
--    setGoals [mv2]
/-
    withMainContext do
    let dcls1 := (←getLCtx).decls
    let d := dcls1.toList.reduceOption.find? fun x =>
      ! ((dcls.toList.reduceOption.map (LocalDecl.toExpr ·)).contains x.toExpr)
    --dbg_trace d.get!.userName
    let guessDegree := ← toNatDegree (fun p => dbg_trace p.getAppFnArgs; mkAppM ``natDegree #[p] <|>
      return mkNatLit 0) pol
    let gds := ← guessDegree.toSyntax
    let _ := ← evalTactic (← `(tactic| refine LE.le.trans (b := $gds) ?_ ?_))
    focusAndDone (← getMainGoal).assumption

    let newGoal := ← (← getMainGoal).clear d.get!.fvarId
--    setGoals (← getGoals)
    setGoals [newGoal]
--/
  --evalTactic (← `(tactic| refine degree_le_natDegree.trans ?_; refine Nat.cast_le.mpr ?_)) <|>
  --  pure ()
  have := degree_le_natDegree.trans (Nat.cast_le.mpr this)
  refine this.trans ?_
  norm_num
    --let gs := ← mv2.apply d.get!.toExpr
  --norm_num
--    let lem := ← mkAppM ``LE.le.trans #[d.get!.toExpr]
--    let _ := ← refineCore (← lem.toSyntax) `ciao true
--    dbg_trace dcls1.size == dcls.size
--    let hyp := ← getFVarLocalDecl nEQ
--    dbg_trace f!"{hyp.type}"
  --assumption
  --refine this.trans ?_
  --clear this
  --linarith [hb]

  --exact natDegree_X_le
  --exact natDegree_X_le
  --refine this.trans ?_
  --simp

/- unworking

partial
def CDL (mv : MVarId) (pol : Expr) : TacticM Unit := do
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
--let mv := ← getMainGoal
setGoals [mv]
let mis := ← match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])  => do
    evalTactic (← `(tactic| refine add ?_ ?_))
--    let Rxargs := Rx.getAppArgs
--    dbg_trace Rxargs
--    let R := Rxargs[0]!
--    let lvl := R.constLevels!
--    dbg_trace f!"levels: {lvl}"
----    let lis := ← mv.apply (← mkConstWithFreshMVarLevels ``add)
--    --let att := ← mkConstWithFreshMVarLevels ``add
--    let att := mkConst ``add [Level.zero] --lvl
--    dbg_trace "before"
--    let _ := ← mv.withContext do
--      dbg_trace ← ppExpr (← getMainTarget)
--      dbg_trace ← isDefEq (← getMainTarget) (← mkConstWithFreshMVarLevels ``add)
--      --let att := ← mkAppM' att #[f, g]
--      dbg_trace "after"
--      dbg_trace ← ppExpr att
    return [f, g].zip (← getGoals)--(← mv.apply (← mkConstWithFreshMVarLevels ``add))
  | (``Neg.neg, #[_, _, f])  =>
--    let lis := ← mv.apply (← mkConstWithFreshMVarLevels ``neg)
    return [f].zip (← getGoals) --(← mv.apply (← mkConstWithFreshMVarLevels ``neg))
  | (``HSub.hSub, #[_, _, _, _, f, g])  =>
--    let lis := ← mv.apply (← mkConstWithFreshMVarLevels ``sub)
    return [f, g].zip (← mv.apply (← mkConstWithFreshMVarLevels ``sub))
  | (``HMul.hMul, #[_, _, _, _, f, g])  =>
--    let lis := ← mv.apply (← mkConstWithFreshMVarLevels ``sub)
    return [f, g].zip (← mv.apply (← mkConstWithFreshMVarLevels ``mul))
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => do
    evalTactic (← `(tactic| refine natDegree_pow_le.trans ?_))
    evalTactic (← `(tactic| refine Nat.mul_le_mul rfl.le ?_))
    pure [(f, ← getMainGoal)]
--    return [f].zip (← mv.apply (← mkConstWithFreshMVarLevels ``pow))
  -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  => do
    let cStx := ← c.toSyntax
    if polFun.isAppOf ``Polynomial.C then
      evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
      pure []
    else if polFun.isAppOf ``Polynomial.monomial then
      evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
      pure []
    else throwError m!"'compute_degree_le' is not implemented for {polFun}"
  | (``Polynomial.X, _)  => do
    dbg_trace "passo da qui"
    evalTactic (← `(tactic| exact natDegree_X_le))
    pure []
  -- deal with `natDegree (n : Nat)`
  | (``Nat.cast, #[_, _, n]) => do
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  -- deal with `natDegree (n : Int)`
  | (``Int.cast, #[_, _, n]) => do
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_int_cast $nStx).le))
    pure []
  -- deal with `natDegree 0, 1, (n : Nat)`.
  -- I am not sure why I had to split `n = 0, 1, generic`.
  | (``OfNat.ofNat, #[_, n, _]) => do
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
      evalTactic (← `(tactic| exact natDegree_one.le)) <|>
      evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"
let _ := mis.mapM fun x => focusAndDone (CDL x.2 x.1)
--let _ := ← newPols.mapM fun x => focus (CDL1 x)

-/
#print

  apply mine
  apply @mine Nat _ _ _ X X
  refine (Polynomial.natDegree_add_le (X : Nat[X]) (X : Nat[X])).trans ?_


#exit


  have nThis : max 0 (2 * (max (max 1 (0 + 1)) 3 + b * 1)) ≤ 10 := sorry
  simp
  apply Nat.le_trans (m := max 0 (2 * (max (max 1 (0 + 1)) 3 + b * 1))) this nThis


--  refine LE.le.trans (?_ : _ ≤ max 0 (2 * (max (max 1 (0 + 1)) 3 + b * 1))) ?_



--    let _ := (← getMainGoal).assert `ciao sideGoal nEQ
    withMainContext do
    let _ := ← mv.setType nEQ
    let ppmv := ← ppExpr (← mv.getType)
    logInfo mv
  --  let _ := ← setGoals [mv]

  sorry
  rename_i hh
  refine hh.trans ?_
  show _ ≤ 2 * (3 + 2)
  simp
  norm_num
elab "compute_degree_le" _x:term :max : tactic => return ()

elab "compute_degree_le" x:term :max " + " y:term : tactic => focus do
  evalTactic (← `(tactic| refine (natDegree_add_le $x $y).trans ?_))
  evalTactic (← `(tactic| refine (max_le_max ?_ ?_)))

/-

def f (n : Nat) : dNat  := n
#check natDegree_add_le
#check natDegree_mul_le
#check @add_le_add
#check max_le_max
-/

elab "compute_degree_le" x:term :max : tactic =>
  evalTactic `(tactic| compute_degree_le refine (natDegree_add_le $x $y).trans ?_)

--elab "compute_degree_le" `(Polynomial.X):term => return ()

elab "compute_degree_le" x:term :max " + " y:term : tactic => focus do
  evalTactic (← `(tactic| refine (natDegree_add_le $x $y).trans ?_))
  evalTactic (← `(tactic| refine (max_le_max ?_ ?_)))
--  elab "compute_degree_le" elabTail:x:term => compute_degree_le $x

elab "compute_degree_le" x:term :max " * " y:term : tactic => focus do
  evalTactic (← `(tactic| refine (natDegree_mul_le (p := $x) (q := $y)).trans ?_))
  evalTactic (← `(tactic| refine add_le_add ?_ ?_))
  evalTactic (← `(tactic| compute_degree_le $x))
  evalTactic (← `(tactic| compute_degree_le $y))

example : natDegree (((X : Int[X]) + X) * C 8) ≤ max 1 1 + 0 := by
  compute_degree_le (X + X) * C 8
  compute_degree_le X + X


/--  `massageNatDegree` assumes that the target is of the form `f.natDegree ≤ d` or `f.degree ≤ d`,
failing otherwise.  If the goal has the required shape, then `massageNatDegree` produces two goals
* `natDegree f ≤ adaptedDegree`, where `adaptedDegree` represents a `Nat` "built like `f`";
* `adaptedDegree ≤ d`, an inequality that hopefully some combination of `norm_num` and `assumption`
  can discharge -- the tactic takes a step to informally verify that the inequality holds.

The tactic returns `[(some f, mv1), (none, mv2)]`, where `mv1` is the metavariable of the goal
`natDegree f ≤ adaptedDegree` and `mv2` is the metavariable of the goal `adaptedDegree ≤ d`.
-/
def massageNatDegree : TacticM (List (Option Expr × MVarId) ) := focus do
  -- if the goal is `degree f ≤ d`, then reduce to `natDegree f ≤ d`.
  evalTactic (← `(tactic| refine degree_le_natDegree.trans ?_; refine Nat.cast_le.mpr ?_)) <|>
    pure ()
  let tgt := ← getMainTarget
  match tgt.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...`
      | (``Polynomial.natDegree, #[_, _, pol]) =>
        -- compute the expected degree, guessing `0` whenever there is a doubt
        let guessDeg := ← toNatDegree (fun p => mkAppM ``natDegree #[p] <|> return mkNatLit 0) pol
        let gdgNat := ← if guessDeg.hasAnyFVar fun _ => true
          then pure 0 else unsafe evalExpr Nat (.const `Nat []) guessDeg
        let rhsNat := ← if rhs.hasAnyFVar fun _ => true
          then pure 0 else unsafe evalExpr Nat (.const `Nat []) rhs
        -- check that the guessed degree really is at most the given degree
        let _ := ← (guard <| gdgNat ≤ rhsNat) <|>
          throwError m!"Should the degree be '{gdgNat}' instead of '{rhsNat}'?"
        let gDstx := ← guessDeg.toSyntax
        -- we begin by replacing the initial inequality with the possibly sharper
        -- `natDegree f ≤ guessDeg`.  This helps, since the shape of `guessDeg` is already
        -- tailored to the expressions that we will find along the way
        evalTactic (← `(tactic| refine le_trans ?_ (?_ : $gDstx ≤ _)))
        return [some pol, none].zip (← getGoals)
--        pure [(some pol, gs[0]!), (none, gs[1]!)]
      | _ => throwError "Expected an inequality of the form 'f.natDegree ≤ d' or 'f.degree ≤ d'"
    | _ => throwError m!"Expected an inequality instead of '{tgt.getAppFnArgs.1}'"
#check Polynomial.X
#check mkAppOptM
example (a : R) [Semiring R] : natDegree (Polynomial.X + X : Int[X]) ≤ max (natDegree (X : Int[X])) (natDegree (X : Int[X])) := by
  run_tac do
    let mv := ← getMainGoal
    let al := ← getLocalDeclFromUserName `a
    let R := ← inferType al.toExpr

--    let polX := ← mkAppM `Polynomial.X #[]
    let polX := ← mkAppOptM `Polynomial.X #[some (mkConst `Int), none]
    let lis := ← mv.apply (← mkAppM `Polynomial.natDegree_add_le #[polX, polX])
  refine Polynomial.natDegree_add_le X X

#check Lean.MVarId.apply
#check refineCore
#eval show MetaM _ from return ppExpr (← inferType (← mkConst' `Polynomial.natDegree_add_le)
#exit
def CDL1 (pmv : Option Expr × MVarId) : TacticM (List (Option Expr × MVarId)) := do
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
if let (some pol, mv) := pmv then
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
    let lis := ← mv.apply (← mkAppM `Polynomial.natDegree_add_le #[f, g])
    let fStx := ← f.toSyntax
    let gStx := ← g.toSyntax
    let lis := ← mv.apply (Expr.const `natDegree_add_le [])
    evalTactic (← `(tactic| refine (natDegree_add_le $fStx $gStx).trans ?_))
    evalTactic (← `(tactic| refine max_le_max ?_ ?_))
    pure [f, g]
  | (``Neg.neg, #[R, _, f])  =>
    let RStx := ← R.toSyntax
    let fStx := ← f.toSyntax
    evalTactic (← `(tactic| refine (natDegree_neg ($fStx : $RStx)).le.trans ?_))
    pure [f]
  | (``HSub.hSub, #[_, _, _, _, f, g])  =>
    let fStx := ← f.toSyntax
    let gStx := ← g.toSyntax
    evalTactic (← `(tactic| refine (natDegree_sub_le $fStx $gStx).trans ?_))
    evalTactic (← `(tactic| refine max_le_max ?_ ?_))
    pure [f, g]
  | (``HMul.hMul, #[_, _, _, _, f, g])  =>
    evalTactic (← `(tactic| refine natDegree_mul_le.trans ?_))
    evalTactic (← `(tactic| refine add_le_add ?_ ?_))
    pure [f, g]
  -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
    let cStx := ← c.toSyntax
    if polFun.isAppOf ``Polynomial.C then
      evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
    else if polFun.isAppOf ``Polynomial.monomial then
      evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
    else throwError m!"'compute_degree_le' is not implemented for {polFun}"
    pure [c]
  | (``Polynomial.X, _)  =>
    evalTactic (← `(tactic| exact natDegree_X_le))
    pure []
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => do
    evalTactic (← `(tactic| refine natDegree_pow_le.trans ?_))
    evalTactic (← `(tactic| refine Nat.mul_le_mul rfl.le ?_))
    pure [f]
  -- deal with `natDegree (n : Nat)`
  | (``Nat.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  -- deal with `natDegree (n : Int)`
  | (``Int.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_int_cast $nStx).le))
    pure []
  -- deal with `natDegree 0, 1, (n : Nat)`.
  -- I am not sure why I had to split `n = 0, 1, generic`.
  | (``OfNat.ofNat, #[_, n, _]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
      evalTactic (← `(tactic| exact natDegree_one.le)) <|>
      evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"
else
pure [pmv]

#check apply
example {K} [Field K] : natDegree ((X : K[X]) ^ 5 + 7 + Polynomial.X + C 0) ≤ 5 := by
  run_tac do
    let polMV := ← massageNatDegree
    let (pols, mvs) := polMV.unzip
    dbg_trace f!"{← pols.reduceOption.mapM (ppExpr ·)}"
    logInfo m!"{mvs}"
  sorry
  norm_num
#check Environment

#exit
partial
def CDL1 (pol : Expr) : TacticM (List Expr) := do
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
    let fStx := ← f.toSyntax
    let gStx := ← g.toSyntax
    evalTactic (← `(tactic| refine (natDegree_add_le $fStx $gStx).trans ?_))
    evalTactic (← `(tactic| refine max_le_max ?_ ?_))
    pure [f, g]
  | (``Neg.neg, #[R, _, f])  =>
    let RStx := ← R.toSyntax
    let fStx := ← f.toSyntax
    evalTactic (← `(tactic| refine (natDegree_neg ($fStx : $RStx)).le.trans ?_))
    pure [f]
  | (``HSub.hSub, #[_, _, _, _, f, g])  =>
    let fStx := ← f.toSyntax
    let gStx := ← g.toSyntax
    evalTactic (← `(tactic| refine (natDegree_sub_le $fStx $gStx).trans ?_))
    evalTactic (← `(tactic| refine max_le_max ?_ ?_))
    pure [f, g]
  | (``HMul.hMul, #[_, _, _, _, f, g])  =>
    evalTactic (← `(tactic| refine natDegree_mul_le.trans ?_))
    evalTactic (← `(tactic| refine add_le_add ?_ ?_))
    pure [f, g]
  -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
    let cStx := ← c.toSyntax
    if polFun.isAppOf ``Polynomial.C then
      evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
    else if polFun.isAppOf ``Polynomial.monomial then
      evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
    else throwError m!"'compute_degree_le' is not implemented for {polFun}"
    pure [c]
  | (``Polynomial.X, _)  =>
    evalTactic (← `(tactic| exact natDegree_X_le))
    pure []
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => do
    evalTactic (← `(tactic| refine natDegree_pow_le.trans ?_))
    evalTactic (← `(tactic| refine Nat.mul_le_mul rfl.le ?_))
    pure [f]
  -- deal with `natDegree (n : Nat)`
  | (``Nat.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  -- deal with `natDegree (n : Int)`
  | (``Int.cast, #[_, _, n]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact (natDegree_int_cast $nStx).le))
    pure []
  -- deal with `natDegree 0, 1, (n : Nat)`.
  -- I am not sure why I had to split `n = 0, 1, generic`.
  | (``OfNat.ofNat, #[_, n, _]) =>
    let nStx := ← n.toSyntax
    evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
      evalTactic (← `(tactic| exact natDegree_one.le)) <|>
      evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
    pure []
  | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"


/--
`CDL` inspects the goal and checks that it is of the form `natDegree f ≤ d` or `degree f ≤ d`,
failing otherwise.  It uses `Mathlib.Tactic.ComputeDegree.toNatDegree` to guess what the `natDegree`
of `f` is and checks that the guess is less than or equal to `d`, failing otherwise.
Finally, it follows the same pattern as `toNatDegree` to recurse into `f`, applying the relevant
theorems to peel off the computation of the degree, one operation at a time.
-/
partial
def CDL : TacticM Unit := do
  -- if there is no goal left, stop
  let _::_ := ← getGoals | pure ()
  let tgt := ← getMainTarget
  match tgt.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``Polynomial.natDegree, #[_, _, pol]) =>
        -- compute the expected degree, guessing `0` whenever there is a doubt
        let guessDeg := ← toNatDegree (fun p => mkAppM ``natDegree #[p] <|> return mkNatLit 0) pol
        let gdgNat := ← if guessDeg.hasAnyFVar fun _ => true
          then pure 0 else unsafe evalExpr Nat (.const `Nat []) guessDeg
        let rhsNat := ← if rhs.hasAnyFVar fun _ => true
          then pure 0 else unsafe evalExpr Nat (.const `Nat []) rhs
        -- check that the guessed degree really is at most the given degree
        let _ := ← (guard <| gdgNat ≤ rhsNat) <|>
          throwError m!"Should the degree be '{gdgNat}' instead of '{rhsNat}'?"
        let gDstx := ← guessDeg.toSyntax
        -- we begin by replacing the initial inequality with the possibly sharper
        -- `natDegree f ≤ guessDeg`.  This helps, since the shape of `guessDeg` is already
        -- tailored to the expressions that we will find along the way
        evalTactic (← `(tactic| refine le_trans ?_ (?_ : $gDstx ≤ _)))
        -- we recurse into the shape of the polynomial, using the appropriate theorems in each case
        match pol.getAppFnArgs with
          | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
            let fStx := ← f.toSyntax
            let gStx := ← g.toSyntax
            evalTactic (← `(tactic| refine (natDegree_add_le $fStx $gStx).trans ?_))
            evalTactic (← `(tactic| refine max_le_max ?_ ?_))
          | (``Neg.neg, #[R, _, f])  =>
            let RStx := ← R.toSyntax
            let fStx := ← f.toSyntax
            evalTactic (← `(tactic| refine (natDegree_neg ($fStx : $RStx)).le.trans ?_))
          | (``HSub.hSub, #[_, _, _, _, f, g])  =>
            let fStx := ← f.toSyntax
            let gStx := ← g.toSyntax
            evalTactic (← `(tactic| refine (natDegree_sub_le $fStx $gStx).trans ?_))
            evalTactic (← `(tactic| refine max_le_max ?_ ?_))
          | (``HMul.hMul, _)  =>
            evalTactic (← `(tactic| refine natDegree_mul_le.trans ?_))
            evalTactic (← `(tactic| refine add_le_add ?_ ?_))
          -- this covers the two cases `natDegree ↑(C c)` and `natDegree (↑(monomial c) _)`
          | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
            let cStx := ← c.toSyntax
            if polFun.isAppOf ``Polynomial.C then
              evalTactic (← `(tactic| refine (natDegree_C $cStx).le))
            else if polFun.isAppOf ``Polynomial.monomial then
              evalTactic (← `(tactic| exact natDegree_monomial_le $cStx))
            else throwError m!"'compute_degree_le' is not implemented for {polFun}"
          | (``Polynomial.X, _)  =>
            evalTactic (← `(tactic| exact natDegree_X_le))
          | (``HPow.hPow, #[_, (.const ``Nat []), _, _, _, _]) => do
            evalTactic (← `(tactic| refine natDegree_pow_le.trans ?_))
            evalTactic (← `(tactic| refine Nat.mul_le_mul rfl.le ?_))
          -- deal with `natDegree (n : Nat)`
          | (``Nat.cast, #[_, _, n]) =>
            let nStx := ← n.toSyntax
            evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
          -- deal with `natDegree (n : Int)`
          | (``Int.cast, #[_, _, n]) =>
            let nStx := ← n.toSyntax
            evalTactic (← `(tactic| exact (natDegree_int_cast $nStx).le))
          -- deal with `natDegree 0, 1, (n : Nat)`.
          -- I am not sure why I had to split `n = 0, 1, generic`.
          | (``OfNat.ofNat, #[_, n, _]) =>
            let nStx := ← n.toSyntax
            evalTactic (← `(tactic| exact natDegree_zero.le)) <|>
              evalTactic (← `(tactic| exact natDegree_one.le)) <|>
              evalTactic (← `(tactic| exact (natDegree_nat_cast $nStx).le))
          | (na, _) => throwError m!"'compute_degree_le' is not implemented for '{na}'"
      -- if the goal is `degree f ≤ d`, then reduce to `natDegree f ≤ d`.
      | (``Polynomial.degree, _) =>
        evalTactic (← `(tactic| refine degree_le_natDegree.trans ?_))
        evalTactic (← `(tactic| refine Nat.cast_le.mpr ?_))
      | _ => throwError "Expected an inequality of the form 'f.natDegree ≤ d' or 'f.degree ≤ d'"
    | _ => throwError m!"Expected an inequality instead of '{tgt.getAppFnArgs.1}'"
/--
`compute_degree_le` attempts to close goals of the form `natDegree f ≤ d` and `degree f ≤ d`.
-/
elab "compute_degree_le1" : tactic => CDL
elab (name := computeDegreeLE) "compute_degree_le" : tactic => focus do
  evalTactic (← `(tactic|
    repeat
    any_goals compute_degree_le1
    any_goals (norm_num <;> try assumption <;> done)))

end Mathlib.Tactic.ComputeDegree
