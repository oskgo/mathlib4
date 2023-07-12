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

open Polynomial

namespace Mathlib.Tactic.ComputeDegree
/-!
The lemmas in the next sections prove an inequality of the form `natDegree f ≤ d` and use
assumptions of the same shape.  This allows a recursive application of the `compute_degree_le`
tactic, on a goal and on all the resulting subgoals.
-/
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

theorem C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem nat_cast_le (n : Nat) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem zero_le : natDegree (↑0 : R[X]) ≤ 0 := natDegree_zero.le
theorem one_le : natDegree (↑1 : R[X]) ≤ 0 := natDegree_one.le

end semiring

section ring
variable [Ring R]

theorem neg {a : Nat} {f : R[X]} (hf : natDegree f ≤ a) : natDegree (- f) ≤ a :=
(natDegree_neg f).le.trans ‹_›

theorem sub {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f - g) ≤ max a b :=
(f.natDegree_sub_le g).trans $ max_le_max ‹_› ‹_›

theorem int_cast_le (n : Int) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

end ring

end mylemmas

open Lean Meta Elab.Tactic

/-- Return `max a b` using `Max.max`. This method assumes `a` and `b` have the same type. -/
def mkMax (a b : Expr) : MetaM Expr := mkAppM ``Max.max #[a, b]

/-- Return `a ^ b` using `HPow.hPow`. -/
def mkPow (a b : Expr) : MetaM Expr := mkAppM ``HPow.hPow #[a, b]

/-- Returns `natDegree pol`. -/
def mkNatDegree (pol : Expr) : MetaM Expr := mkAppM ``natDegree #[pol]
/-- Returns `degree pol`. -/
def mkDegree (pol : Expr) : MetaM Expr := mkAppM ``degree #[pol]

def _root_.Lean.SourceInfo.ctorName : Lean.SourceInfo → String
  | .original .. => "original"
  | .synthetic _ _ _ => "synthetic"
  | .none => "none"

def _root_.Lean.Syntax.ctorName : Syntax → String
  | .missing  => "missing"
  | .node ..  => "node"
  | .atom ..  => "atom"
  | .ident .. => "ident"

def _root_.Lean.Syntax.getIdent : Syntax → Name
  | .ident _si _rv val _pr =>
    --dbg_trace f!"si: {si.ctorName}\npreresolved: {pr.length}\nraw value: {rv}"
    val
  | _ => .anonymous

def _root_.Lean.Syntax.getString : Syntax → String
  | .atom _ val => val
  | _ => ""

def _root_.Lean.Syntax.getVal : Syntax → Name
  | .ident _ _ val _ => val
  | _ => .anonymous

--def _root_.Lean.Syntax.getArgs : Syntax → Array Syntax
--  | .node _ _ arr  => arr
--  | _ => #[]

declare_syntax_cat di

syntax "s0" : di
syntax "sℕ" : di
syntax "sℤ" : di
syntax "sC" : di
syntax "sX" : di
syntax:max " ( " di " ) " : di
syntax:65 di " + " di:66 : di
syntax:65 di " - " di:66 : di
syntax:70 di " * " di:71 : di
syntax:75 "- " di:76 : di
syntax:80 di " ^ " term:81 : di
syntax:75 "sM " term:76 : di

#check (s0 : TSyntax `di)

syntax "[di|" di "]" : term


open Lean Elab Term

def polToDegInfo (pol : Expr) : TermElabM (Name × TSyntax `term) :=
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])                 => do
    let (_, fs) := ← polToDegInfo f
    let (_, gs) := ← polToDegInfo g
    let fg := ← `(fs + gs)
    pure (``add, fg)
  | (``Neg.neg,   #[_, _, f])                          => - (polToDegInfo f)
  | (``HSub.hSub, #[_, _, _, _, f, g])                 => (polToDegInfo f) - (polToDegInfo g)
  | (``HMul.hMul, #[_, _, _, _, f, g])                 => (polToDegInfo f) * (polToDegInfo g)
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, n]) => (polToDegInfo f) ^ n
  | (``Polynomial.X, _)                                => .X
  | (``Nat.cast, #[_, _, _n])                          => .natCast
  | (``Int.cast, #[_, _, _n])                          => .intCast
  -- why should I split `n = 0` from generic `n`?
  | (``OfNat.ofNat, #[_, (.lit (.natVal 0)), _])       => .ofNatZero
  | (``OfNat.ofNat, #[_, _n, _])                       => .ofNat
  -- deal with `monomial` and `C`
  | (``FunLike.coe, #[_, _, _, _, polFun, c]) => match polFun.getAppFnArgs with
    | (``Polynomial.monomial, _)                       => .monomial c
    | (``Polynomial.C, _)                              => .C
    | _ => .err polFun
  -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
  | (_na, _) => .rest pol



def toName : DegInfo → Name
  | .rest _     => ``le_rfl
  | .X          => ``natDegree_X_le
  | .natCast    => ``nat_cast_le
  | .intCast    => ``int_cast_le
  | .ofNatZero  => ``zero_le
  | .ofNat      => ``nat_cast_le
  | .C          => ``C_le
  | .monomial _ => ``natDegree_monomial_le
  | .neg _      => ``neg
  | .add ..     => ``add
  | .sub ..     => ``sub
  | .mul ..     => ``mul
  | .pow ..     => ``pow
  | .err _      => .anonymous


--#check [di| C * X ^ 4 - Nat * zero]

partial
def toN : TSyntax `di → Nat
--  | `([di|$a + $b]) => toN a + toN b
--  | `(_X:di) => 1
--  | `($a:di) => 1
  | _ => 0

#check toN
#check toN [di|sX + sX]

variable (n z c x : Int)
macro_rules
  | `([di|$a + $b]) => `([di|$a] + [di|$b])
  | `([di|$a * $b]) => `([di|$a] * [di|$b])
  | `([di|$a ^ $b]) => `([di|$a] ^ $b)
  | `([di|$a - $b]) => `([di|$a] - [di|$b])
  | `([di|($a)])    => `(- [di|$a])
  | `([di|- $a])    => `(- [di|$a])
  | `([di|s0])    => `(0)
  | `([di|sℕ])    => `(n)
  | `([di|sℤ])    => `(z)
  | `([di|sC])      => `(c)
  | `([di|sX])      => `(x)
  | `([di|sM $t]) => `(x ^ $t)
--def toaN : Syntax → Nat




def tos (stx : TSyntax `term) (val : String := "") : Bool :=
if (stx.raw.getArg 0).getVal == `Expr.fvar then true
else
  let enter := ((((((((stx.raw.getArg 1).getArg 1).getArg 1).getArg 1).getArg 1).getArg 0).getArg 1).getArg 0).getArg 0
--    let fin : TSyntax `num := { raw := enter }
--{b.raw.ctorName}
--{b.raw.getArgs.map Lean.Syntax.ctorName}
--{b.raw.getArgs}
--{enter.map Lean.Syntax.ctorName}
--enter: {enter.size}
--fin: {fin.raw}
--    dbg_trace f!"** {enter} **
--enterctor: {enter.ctorName}
--bctor: {b.raw.ctorName}
--b infoctor: {b.raw.getHeadInfo.ctorName}
--actor: {a.raw.ctorName}
--"
  let astr := enter.getString
  let n := astr.toNat!
--    dbg_trace f!"string: {astr}"
--  let araw := mkAtom astr
--  let araw := Syntax.atom b.raw.getHeadInfo astr
--    let araw := b.raw.setArgs #[enter]
--    let ato : TSyntax `term := ⟨araw⟩
  dbg_trace (val ++ f!"{n}")
--    dbg_trace f!"ato: {ato}"
--    if n < 100 then
--      `($a ^ $ato)
--    else
--      `($a ^ big)
--  dbg_trace (araw == fin)
--  `($ato)
  false

/--
`DegInfo` is the type containing the part of the syntax tree of a polynomial that currently
plays a role in the computation of its degree.
-/
inductive DegInfo where
  /-- `.rest pol` is a node where `f` is typically an `fvar`.  It corresponds to `natDegree pol`. -/
  | rest      : Expr → DegInfo
  /-- `.X` is a node representing `X`.  It corresponds to `1`. -/
  | X         : DegInfo
  /-- `.natCast` is a node representing a `Nat`.  It corresponds to `0`. -/
  | natCast   : DegInfo
  /-- `.intCast` is a node representing an `Int`.  It corresponds to `0`. -/
  | intCast   : DegInfo
  /-- `.ofNatZero` is a node representing the literal `0`.  It corresponds to `0`. -/
  | ofNatZero : DegInfo
  /-- `.ofNat` is a node representing a `OfNat`.  It corresponds to `0`. -/
  | ofNat     : DegInfo
  /-- `.C` is a node representing `C x`.  It corresponds to `0`. -/
  | C         : DegInfo
  /-- `.monomial n` is a node representing a `↑(monomial n) _`.  It corresponds to `n`. -/
  | monomial  : Expr → DegInfo
  /-- `.neg pol` is a node representing `- pol`.  It corresponds to `natDegree pol`. -/
  | neg       : DegInfo → DegInfo
  /-- `.add f g` is a node representing `f + g`.
      It corresponds to `max (natDegree f) (natDegree g)`. -/
  | add       : DegInfo → DegInfo → DegInfo
  /-- `.sub f g` is a node representing `f - g`.
      It corresponds to `max (natDegree f) (natDegree g)`. -/
  | sub       : DegInfo → DegInfo → DegInfo
  /-- `.mul f g` is a node representing `f * g`.
      It corresponds to `(natDegree f) + (natDegree g)`. -/
  | mul       : DegInfo → DegInfo → DegInfo
  /-- `.pow f n` is a node representing `f ^ n`.
      It corresponds to `n * (natDegree f)`. -/
  | pow       : DegInfo → Expr → DegInfo
  /-- `.err e` is a node for error-management.
      The `Expr`ession `e` is data useful to report the error. -/
  | err       : Expr → DegInfo
  deriving BEq, Inhabited, ToExpr

@[app_unexpander DegInfo.add] def unexpand_add : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a + $b)
  | _ => throw ()

@[app_unexpander DegInfo.mul] def unexpand_mul : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a * $b)
  | _ => throw ()

@[app_unexpander DegInfo.neg] def unexpand_neg : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `(- $a)
  | _ => throw ()

@[app_unexpander DegInfo.sub] def unexpand_sub : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => `($a - $b)
  | _ => throw ()

@[app_unexpander DegInfo.pow] def unexpand_pow : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b) => if tos b "exp: " then `($a ^ nnn) else `($a ^ lit)
  | _ => throw ()

@[app_unexpander DegInfo.C] def unexpand_C : Lean.PrettyPrinter.Unexpander
  | `($_) => `(‹C›)

@[app_unexpander DegInfo.X] def unexpand_X : Lean.PrettyPrinter.Unexpander
  | `($_) => `(‹X›)

@[app_unexpander DegInfo.ofNat] def unexpand_ofNat : Lean.PrettyPrinter.Unexpander
  | `($_) => `(‹ofℕ›)

@[app_unexpander DegInfo.natCast] def unexpand_natCast : Lean.PrettyPrinter.Unexpander
  | `($_) => `(‹ℕ›)

@[app_unexpander DegInfo.intCast] def unexpand_intCast : Lean.PrettyPrinter.Unexpander
  | `($_) => `(‹ℤ›)

@[app_unexpander DegInfo.rest] def unexpand_rest : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => do
    match a.raw with
    | .atom ..  => `(‹ato›)
    | .ident .. => `(‹ide›)
    | .node ..  => `(‹node›)
    | _         => `(‹$a›)
  | _ => throw ()

@[app_unexpander DegInfo.monomial] def unexpand_monomial : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => if tos a "monomial: " then `(monomial nnn) else `(monomial lit)
  | _ => throw ()

instance : HAdd DegInfo DegInfo DegInfo where hAdd := .add
instance : HMul DegInfo DegInfo DegInfo where hMul := .mul
instance : Neg DegInfo                  where neg := .neg
instance : HSub DegInfo DegInfo DegInfo where hSub := .sub
instance : Pow DegInfo Expr             where pow := .pow

/-- `polToDegInfo pol` converts an `Expr`ession `pol` representing a polynomial to the
corresponding "tree object" of Type `DegInfo`.
`polToDegInfo` recurses into `pol`, extracting the data it needs to build the associated `DegInfo`.
-/
partial
def polToDegInfo (pol : Expr) : DegInfo :=
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])                 => (polToDegInfo f) + (polToDegInfo g)
  | (``Neg.neg,   #[_, _, f])                          => - (polToDegInfo f)
  | (``HSub.hSub, #[_, _, _, _, f, g])                 => (polToDegInfo f) - (polToDegInfo g)
  | (``HMul.hMul, #[_, _, _, _, f, g])                 => (polToDegInfo f) * (polToDegInfo g)
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, n]) => (polToDegInfo f) ^ n
  | (``Polynomial.X, _)                                => .X
  | (``Nat.cast, #[_, _, _n])                          => .natCast
  | (``Int.cast, #[_, _, _n])                          => .intCast
  -- why should I split `n = 0` from generic `n`?
  | (``OfNat.ofNat, #[_, (.lit (.natVal 0)), _])       => .ofNatZero
  | (``OfNat.ofNat, #[_, _n, _])                       => .ofNat
  -- deal with `monomial` and `C`
  | (``FunLike.coe, #[_, _, _, _, polFun, c]) => match polFun.getAppFnArgs with
    | (``Polynomial.monomial, _)                       => .monomial c
    | (``Polynomial.C, _)                              => .C
    | _ => .err polFun
  -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
  | (_na, _) => .rest pol

example
  {f : Int[X]} {n : Nat} : f * - 4 - (C 0 : Int[X]) * X ^ 10 * X ^ n + monomial 4 5 = 0 := by
  run_tac do
    let tgt := ← getMainTarget
    if let some (t, lhs, rhs) := tgt.eq? then
      --dbg_trace ← ppExpr lhs
      let tf := polToDegInfo lhs
      --dbg_trace ToExpr.toExpr tf
      let ppe := ← ppExpr (ToExpr.toExpr (tf))
      logInfo ppe
  sorry

example {f : Int[X]} {n : Nat} : natDegree (4 - (C 1 : Int[X]) * X ^ 10) ≤ 10 := by
  apply (natDegree_sub_le _ _).trans






def toName : DegInfo → Name
  | .rest _     => ``le_rfl
  | .X          => ``natDegree_X_le
  | .natCast    => ``nat_cast_le
  | .intCast    => ``int_cast_le
  | .ofNatZero  => ``zero_le
  | .ofNat      => ``nat_cast_le
  | .C          => ``C_le
  | .monomial _ => ``natDegree_monomial_le
  | .neg _      => ``neg
  | .add ..     => ``add
  | .sub ..     => ``sub
  | .mul ..     => ``mul
  | .pow ..     => ``pow
  | .err _      => .anonymous

variable (alt : Expr → MetaM Expr) in
def toNatDegree : DegInfo → MetaM Expr
  | .rest e     => alt e
  | .X          => return mkNatLit 1
  | .natCast    => return mkNatLit 0
  | .intCast    => return mkNatLit 0
  | .ofNatZero  => return mkNatLit 0
  | .ofNat      => return mkNatLit 0
  | .C          => return mkNatLit 0
  | .monomial n => return n
  | .neg f      => toNatDegree f
  | .add f g    => do mkMax (← toNatDegree f) (← toNatDegree g)
  | .sub f g    => do mkMax (← toNatDegree f) (← toNatDegree g)
  | .mul f g    => do mkAdd (← toNatDegree f) (← toNatDegree g)
  | .pow f n    => do mkMul n (← toNatDegree f)
  | .err p      => throwError m!"'compute_degree_le' is not implemented for {p}"

--  TODO: is it useful to return the last `Expr`, namely `rhs`, representing the target degree?
def isDegLE (e : Expr) : CoreM (Bool × Expr) := do
  match e.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, _rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``degree, #[_, _, pol])    => return (false, pol)
      | (``natDegree, #[_, _, pol]) => return (true, pol)
      | (na, _) => throwError (f!"Expected an inequality of the form\n\n" ++
        f!"  'f.natDegree ≤ d'  or  'f.degree ≤ d',\n\ninstead, {na} appears on the LHS")
    | _ => throwError m!"Expected an inequality instead of '{e.getAppFnArgs.1}'"

--#check degree (X : Nat[X]) ≤ (1 : Nat)
--#check WithBot

/-- `mkNatDegreeLE f is_natDeg?` is an expression representing eith `natDegree f ≤ guessDegree f`
or `degree f ≤ guessDegree f`, depending on whether `is_natDeg?` is `true` or `false`. -/
--  todo: the equality `di = polToDegInfo f` should hold.  possibly fix this -- can I only pass one,
--  without recomputing the other?
def mkNatDegreeLE (f : Expr) (di : DegInfo) (is_natDeg? : Bool) : MetaM Expr := do
  let guessDegree := ← toNatDegree (fun p => dbg_trace p.getAppFnArgs; mkNatDegree p <|>
    return mkNatLit 0) di
  let guessDegree := ← if is_natDeg? then
    return guessDegree
  else
    let wBotN := Expr.app (Expr.const ``WithBot [Level.zero]) (Expr.const ``Nat [])
    mkAppOptM ``Nat.cast #[some wBotN, none, some guessDegree]
  let ndf := ← if is_natDeg? then mkNatDegree f else mkDegree f
  let ndfLE := ← mkAppM ``LE.le #[ndf, guessDegree]
  pure ndfLE

def one_step_compute_degree_le (pol : DegInfo) (mv : MVarId) :
    MetaM (List (Bool × Expr × MVarId)) := do

--  let (na, exs) := toName pol
  let na := toName pol
  let mvs := ← if na.isAnonymous then return [mv] else mv.applyConst na
  return (List.replicate mvs.length na.isSome).zip (exs.zip mvs)

partial
def recurse_compute_degree (l : List (Bool × Expr × MVarId)) : MetaM (List (Expr × MVarId)) := do
  let (bs , rest) := l.unzip
  if true ∈ bs then
    let news := ← l.mapM fun x@(act?, pol, mv) =>
      if act? then one_step_compute_degree_le pol mv else pure [x]
    recurse_compute_degree news.join
  else
    pure rest
    --ASCDL (← l.mapM fun x@(act?, pol, mv) => if act? then OSCDL pol mv else pure [x])


example {f : Nat[X]} : f + 2 = 0 := by
  run_tac do
    let tgt := ← getMainTarget
    if let some (_, lhs, rhs) := tgt.eq? then
      let di := polToDegInfo lhs
      let degExpr := ← toNatDegree mkNatDegree (di + di ^ (mkNatLit 3))
      dbg_trace ← ppExpr degExpr




structure DegreeInfo where
  (add : List Expr)
  (neg : List Expr)
  (sub : List Expr)
  (mul : List Expr)
  (pow : List Expr)
  (natDegree_X_le : List Expr)
  (nat_cast_le : List Expr)
  (int_cast_le : List Expr)
  (ofNatZero : List Expr)
  (ofNat : List Expr)
  (C : List Expr)
  (monomial : List Expr)
  (rest : List Expr)

#check MVarId
#exit
def assign_lemma_name (pol : Expr) : Option Name × (List Expr) :=
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])                 => (``add, [f,g])
  | (``Neg.neg,   #[_, _, f])                          => (``neg, [f])
  | (``HSub.hSub, #[_, _, _, _, f, g])                 => (``sub, [f,g])
  | (``HMul.hMul, #[_, _, _, _, f, g])                 => (``mul, [f,g])
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => (``pow, [f])
  | (``Polynomial.X, _)                                => (``natDegree_X_le, [pol])
  | (``Nat.cast, #[_, _, n])                           => (``nat_cast_le, [n])
  | (``Int.cast, #[_, _, n])                           => (``int_cast_le, [n])
  -- why should I split `n = 0` from generic `n`?
  | (``OfNat.ofNat, #[_, n@(.lit (.natVal 0)), _])     => (``zero_le, [n])
  | (``OfNat.ofNat, #[_, n, _])                        => (``nat_cast_le, [n])
  -- deal with `monomial` and `C`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
    if polFun.isAppOf ``Polynomial.C then                 (``C_le, [c])
    else if polFun.isAppOf ``Polynomial.monomial then     (``natDegree_monomial_le, [c])
    -- consider `throwError m!"'compute_degree_le' is not implemented for {polFun}"`
    else                                                  (none, [pol])
  -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
  | (_na, _) => (none, [pol])













/-- `toNatDegree alt pol` takes a function `alt : Expr → MetaM Expr` and `pol : Expr` as inputs.
It assumes that `pol` represents a polynomial and guesses an `Expr` for its `natDegree`.
It errs on the side of assuming "no cancellation/generic nontriviality", e.g. it guesses
`natDegree (0 * X) = 1` and `natDegree X = 1`, regardless of whether the base-ring is `nontrivial`
or not.
Everything that is not obtained as an iterated sum, product or `Nat`-power of `C`onstants, `Nat`s,
`X`s, `monomials` is outsourced to the function `alt`.

Chances are that `alt` is the function that, for an expression `f`, guesses the `Expr`ession
representing `natDegree f`.

(Another possible choice would be `mkNatLit 0`, though this is not what `compute_degree_le` does.)
-/
partial
def toNatDegree (alt : Expr → MetaM Expr) (pol : Expr) : MetaM Expr :=
match pol.getAppFnArgs with
  --  we assign a `natDegree` to the `Nat`s, the `Int`s, the `C`onstants and `X`
  | (``OfNat.ofNat, _) =>  return mkNatLit 0
  | (``Nat.cast, _) =>     return mkNatLit 0
  | (``Int.cast, _) =>     return mkNatLit 0
  | (``Polynomial.X, _) => return mkNatLit 1
  | (``Neg.neg, #[_, _, a]) =>    toNatDegree alt a
  --  we assign a `natDegree` to the powers: `natDegree (a ^ b) = b * natDegree a`
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
  --  we assign `natDegree` `n` to `↑(monomial n) _`;
  --  we assign `natDegree` `0` to `C n`;
  --  falling back to `alt pol`, if the `FunLike.coe` was not `monomial` or `C`
  | (``FunLike.coe, #[_, _, _, _, fn, _]) => match fn.getAppFnArgs with
    | (``monomial, #[_, _, n]) => return n
    | (``C, _) =>                 return mkNatLit 0
    | _ => alt pol
  --  everything else falls back to `alt pol`.
  | (_name, _args) => alt pol

def assign_lemma_name (pol : Expr) : Option Name × (List Expr) :=
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])                 => (``add, [f,g])
  | (``Neg.neg,   #[_, _, f])                          => (``neg, [f])
  | (``HSub.hSub, #[_, _, _, _, f, g])                 => (``sub, [f,g])
  | (``HMul.hMul, #[_, _, _, _, f, g])                 => (``mul, [f,g])
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) => (``pow, [f])
  | (``Polynomial.X, _)                                => (``natDegree_X_le, [pol])
  | (``Nat.cast, #[_, _, n])                           => (``nat_cast_le, [n])
  | (``Int.cast, #[_, _, n])                           => (``int_cast_le, [n])
  -- why should I split `n = 0` from generic `n`?
  | (``OfNat.ofNat, #[_, n@(.lit (.natVal 0)), _])     => (``zero_le, [n])
  | (``OfNat.ofNat, #[_, n, _])                        => (``nat_cast_le, [n])
  -- deal with `monomial` and `C`
  | (``FunLike.coe, #[_, _, _, _, polFun, c])  =>
    if polFun.isAppOf ``Polynomial.C then                 (``C_le, [c])
    else if polFun.isAppOf ``Polynomial.monomial then     (``natDegree_monomial_le, [c])
    -- consider `throwError m!"'compute_degree_le' is not implemented for {polFun}"`
    else                                                  (none, [pol])
  -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
  | (_na, _) => (none, [pol])

def one_step_compute_degree_le (pol : Expr) (mv : MVarId) :
    MetaM (List (Bool × Expr × MVarId)) := do
  let (na, exs) := assign_lemma_name pol
  let mvs := ← if na.isSome then mv.applyConst na.get! else return [mv]
  return (List.replicate mvs.length na.isSome).zip (exs.zip mvs)

partial
def recurse_compute_degree (l : List (Bool × Expr × MVarId)) : MetaM (List (Expr × MVarId)) := do
  let (bs , rest) := l.unzip
  if true ∈ bs then
    let news := ← l.mapM fun x@(act?, pol, mv) =>
      if act? then one_step_compute_degree_le pol mv else pure [x]
    recurse_compute_degree news.join
  else
    pure rest
    --ASCDL (← l.mapM fun x@(act?, pol, mv) => if act? then OSCDL pol mv else pure [x])

example : natDegree (↑(0) : Int[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example : natDegree (0 : Nat[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example : natDegree (1 : Nat[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example : natDegree (1 : Int[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example {n : Nat} : natDegree (n : Nat[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example {n : Nat} : natDegree (n : Int[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example {n : Int} : natDegree (↑(n) : Int[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

example {f g : Int[X]} (hf : natDegree f ≤ 1) (hg : natDegree g ≤ 2) :
    natDegree (- (X ^ 2 * f + (g * g ^ 2)) + ( (↑(-1) : Int[X]) * monomial 3 2)) ≤ 6 := by
  run_tac do
    let tgt := ← getMainTarget
    let goal := ← getMainGoal
    let (isNatDeg?, pol) := ← isDegLE (← getMainTarget)
    let x := ← mkNatDegreeLE pol isNatDeg?
    let stx := ← x.toSyntax
    evalTactic (← `(tactic| have : $stx))
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    let gs := ← getGoals
    setGoals (goal :: gls.unzip.2 ++ gs)
  any_goals apply rfl.le
  rename_i this
  conv_rhs at this => norm_num

  apply this.trans
  norm_num
  constructor <;>
  try linarith





example {f g : Int[X]} (hf : natDegree f ≤ 1) (hg : natDegree g ≤ 2) :
    natDegree (- (X ^ 2 * f + (g * g ^ 2)) + ( (↑(-1) : Int[X]) * monomial 3 2)) ≤ max (max ((2 * 1) + 1) (2 + 2 * 2)) (0 + 3) := by
  run_tac do
    let tgt := ← getMainTarget
    let goal := ← getMainGoal
--    dbg_trace tgt.ctorName
--    dbg_trace tgt.getAppFnArgs
    match tgt.getAppFnArgs with
      | (``LE.le, #[_, _, lhs, rhs]) =>
        let (isNatDeg?, pol) := ← isDegLE (← getMainTarget)
        let x := ← mkNatDegreeLE pol isNatDeg?
        let stx := ← x.toSyntax
        evalTactic (← `(tactic| have : $stx))
--        dbg_trace ← isDefEq x rhs
--    dbg_trace x
        let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
--    let gls := ← CDLmv pol (← getMainGoal)
--    let gls := ← CDLmv gls[0]!.1 gls[0]!.2
--        let meq := ← mkEq x rhs
--        dbg_trace "   here"
--        dbg_trace ← ppExpr x
        let gs := ← getGoals
        setGoals (goal :: gls.unzip.2 ++ gs)
--        setGoals [goal]
      | _ => pure ()
--  exact?
  any_goals apply rfl.le
  rename_i this
  conv_rhs at this => norm_num

  apply this.trans
  sorry
--  norm_num
--  constructor <;>
--  linarith

--  any_goals assumption


example {f g : Int[X]} (hf : natDegree f ≤ 1) (hg : natDegree g ≤ 2) :
    natDegree (- (X ^ 2 * f + (g * g ^ 2)) + ( (↑(-4) : Int[X]) * monomial 3 2)) ≤ max (max ((2 * 1) + 1) (2 + 2 * 2)) (0 + 3) := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
--    let gls := ← CDLmv pol (← getMainGoal)
--    let gls := ← CDLmv gls[0]!.1 gls[0]!.2

    setGoals gls.unzip.2
  any_goals assumption
  --apply (natDegree_nat_cast _).le



example [Semiring R] (n : Nat) : natDegree (n : R[X]) ≤ 0 := by
  run_tac do
    let (_, pol) := ←  isDegLE (← getMainTarget)
    let gls := ← recurse_compute_degree [(true, pol, (← getMainGoal))]
    setGoals gls.unzip.2

#exit
#check evalSkip
#check MVarId.applyConst
#check LocalContext
#check Lean.MVarId.apply

#check List.replicate


partial
def CDLmv (pol : Expr) (mv : MVarId) : MetaM (List (Expr × MVarId)) := do
--if pol.isFVar then pure [(pol, mv)] else
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
let (na, exs) := dict pol
let oneStep := ← do
  let mvs := ← if na.isSome then mv.applyConst na.get! else return [mv]
  return (exs.zip mvs)
let allSteps := ← oneStep.mapM fun x => match na.isSome, x with
  | true, (newPol, newMVarId) => CDLmv newPol newMVarId
  | false, _ => do mv.assumption; pure []
return allSteps.join


/-  was working, no dictionary
partial
def CDLmv (pol : Expr) (mv : MVarId) : MetaM (List (Expr × MVarId)) := do
--if pol.isFVar then pure [(pol, mv)] else
-- we recurse into the shape of the polynomial, using the appropriate theorems in each case
let oneStep := ← do match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])  =>
--    let mvs := ← mv.applyConst ``add
    let (na, exs) := dict pol
    return ([f,g].zip mvs).map (some ·)
  | (``Neg.neg, #[_, _, f])  =>
    let mvs := ← mv.applyConst ``neg
    return [(f, mvs[0]!)]
  | (``HSub.hSub, #[_, _, _, _, f, g])  =>
    let mvs := ← mv.applyConst ``sub
    return [f,g].zip mvs
  | (``HMul.hMul, #[_, _, _, _, f, g])  =>
    let mvs := ← mv.applyConst ``mul
    return [f,g].zip mvs
  | (``HPow.hPow, #[_, (.const ``Nat []), _, _, f, _]) =>
    let mvs := ← mv.applyConst ``pow
    return [(f, mvs[0]!)]
  | _ => return [none]
  --throwError f!"'compute_degree' unimplemented for Expr.{pol.ctorName}, ({e.1}, {e.2})"
let allSteps := ← oneStep.mapM fun x => match x with
    | some (newPol, newMVarId) => (CDLmv newPol newMVarId) --.join
    | none => pure [(pol, mv)]
return allSteps.join

-/


#exit

--  consider using this to introduce new hypotheses
#check Lean.MVarId.assertHypotheses


/-- `CDL pol` assumes that `pol` is the `Expr`ession representing a polynomial and that
the current goal is `natDegree pol ≤ d`, where `d` is the result of `toNatDegree pol`.
It recursed into the shape of the `Expr`ession `pol` and applies the appropriate lemmas to
make as much progress as possible. -/
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
let _ := ← newPols.mapM fun x => focus (CDL x)

section withStx
variable (stx : TSyntax `Mathlib.Tactic.optBinderIdent)

def addNatDegreeDecl (pol : Expr) (is_natDeg? : Bool) : TacticM Unit := focus do
  let nEQ := ← mkNatDegreeLE pol is_natDeg?
  let nEQS := ← nEQ.toSyntax
--  let ns : TSyntax `Mathlib.Tactic.optBinderIdent := { raw := mkAtom "" }
  let (mv1, mv2) := ← haveLetCore (← getMainGoal) stx #[] (some nEQS) true
  setGoals [mv1, mv2]
  if ! is_natDeg? then
    evalTactic (← `(tactic| refine degree_le_natDegree.trans ?_; refine Nat.cast_le.mpr ?_))
  focusAndDone $ CDL pol

open Elab Term in
def fAdd (is_natDeg? : Bool) (t : TSyntax `term) : TacticM Unit := do
  let te := ← withRef t do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVars false
    instantiateMVars e
  addNatDegreeDecl stx te is_natDeg?
  let ni : TSyntax `ident :=
    if stx.raw[0].isIdent then ⟨stx.raw[0]⟩ else HygieneInfo.mkIdent ⟨stx.raw[0]⟩ `this
  --let n := stx.raw[0].getId --optBinderIdent.name n
  evalTactic (← `(tactic| conv_rhs at $ni => { norm_num }))

end withStx

syntax "natDeg" haveIdLhs' : tactic
syntax "deg" haveIdLhs' : tactic

open Elab Term in
elab_rules : tactic
| `(tactic| natDeg $n:optBinderIdent : $t:term) => do
  fAdd n true t
| `(tactic| deg $n:optBinderIdent : $t:term) => do
  fAdd n false t
--  let te := ← withRef t do
--    let e ← Term.elabTerm t none
--    Term.synthesizeSyntheticMVars false
--    instantiateMVars e
--  addNatDegreeDecl n te true
--  let ni : TSyntax `ident :=
--    if n.raw[0].isIdent then ⟨n.raw[0]⟩ else HygieneInfo.mkIdent ⟨n.raw[0]⟩ `this
--  --let n := n.raw[0].getId --optBinderIdent.name n
--  evalTactic (← `(tactic| conv_rhs at $ni => { norm_num }))
/-
elab_rules : tactic
| `(tactic| natDeg $n:optBinderIdent $bs* $[: $t:term]?) => do
  let (goal1, goal2) ← haveLetCore (← getMainGoal) n bs t false
  replaceMainGoal [goal1, goal2]
-/

#check assumption
#check clear
theorem what :
    let pol : Int[X] :=(X + (- X)) ^ 2 - monomial 5 8 * X ^ 4 * X + C 5 - 7 + (-10)
    degree pol ≤ 10 ∧ natDegree pol ≤ 10 := by
  natDeg ndf : (((X : Int[X]) + (- X)) ^ 2 - monomial 5 8 * X ^ 4 * X + C 5 - 7 + (-10))
  deg df : (((X : Int[X]) + (- X)) ^ 2 - monomial 5 8 * X ^ 4 * X + C 5 - 7 + (-10))
  --conv_rhs at df => { norm_num }
  exact ⟨df, ndf⟩
  --stop

#eval 0

open Expr in
variable (e : Expr) in
def myfind : Expr → MetaM (List Expr)
  | tot@(.app fn arg) => do
    let tail := (← myfind fn) ++ (← myfind arg)
    let head := if ← isDefEq e fn then [fn] else []
    let head := head ++ if ← isDefEq e arg then [tot] else []
    return head ++ tail
  | f => do if ← isDefEq e f then pure [f] else pure []

#check elabTerm
#check instToExprSyntax
def ff (t : Expr) /-(stx : TSyntax `term)-/ (pot : List Expr) : MetaM (List Expr) := do
  pot.filterM fun d => do
--    dbg_trace ← ppExpr (ToExpr.toExpr (stx : Syntax))
--    isDefEq (ToExpr.toExpr (stx : Syntax)) d
    isDefEq t d

macro "foo" n:num a:term:arg : term =>
  `(show $(Lean.quote (n.getNat+1)) ≤ $a ∨ $a ≤ $n from Nat.lt_or_ge ..)

example (a : Nat) : True := by
  have := foo 37 a -- infoview shows `this: 38 ≤ a ∨ a ≤ 37`
  sorry


#eval show MetaM Unit from do
  let bv := Expr.bvar 0
  dbg_trace  s!"{bv.isAppOf `Nat}"
  dbg_trace  s!"dbg_trace  {bv}"
  logInfo    s!"logInfo    {bv}"
  IO.println s!"IO.println {bv}"
--  let wf := ← whnf bv

partial
def findPol (ini : Expr) : MetaM (List Expr) := do
let tName : Name := `Polynomial
--if ini.binderInfo != .default then dbg_trace f!"++++++++++++++** ini:   {ini.ctorName} + {← ppExpr ini} + {ini.binderInfo == .default}"
dbg_trace f!"more {ini}"
if (ini.ctorName == `forallE || ini.ctorName == `bvar) then
  return [ini]
else
let tin := ← inferType ini
dbg_trace f!"this is tin: {← ppExpr tin}"
let wini := ← if (ini.ctorName == `forallE || ini.ctorName == `bvar) then pure ini else whnf ini
let res := if tin.isAppOf tName then [ini] else []
dbg_trace f!"** wini: {wini.ctorName} + {wini}"
dbg_trace f!"***** match on '{← ppExpr wini}'"
match wini with
--  | `(OfNat.ofNat ..) => return res
  | .app fn arg    => dbg_trace f!"       fn is {fn}     arg is {arg}";return res ++ (← findPol fn) ++ (← findPol arg)
--  | .lam _ bt bd _ => return res ++ (← findPol bt) ++ (← findPol bd)
  | _              => return res

#check Environment
irreducible_def st {R : Type _} [Ring R] (_f : R[X]) : Bool := true

#eval show MetaM Unit from do
  let cst := (Expr.const `ciao [])
  let wc := ← whnf cst
  dbg_trace cst
  dbg_trace ← ppExpr wc

def _root_.st1 (_p : Nat[X]) : Prop := true
variable (f : Nat[X])
example : --[Semiring R] [Subsingleton R] {a b : R} {f g : R[X]} :
  f = f --∧ (∀ y : R[X], (X : R[X]) = y)
   := by
  run_tac do
    let goal := ← getMainTarget
    --dbg_trace (← whnfR goal).ctorName
    --dbg_trace ← ppExpr goal
    --dbg_trace "***  here  ***"
    let founds := ← findPol (goal)
    let ppfounds := ← founds.mapM (ppExpr ·)
    dbg_trace f!"Length of the list: {ppfounds.length}"
    dbg_trace f!"**  types.findPol:\n{ppfounds}"

  intros
  refine ((subsingleton_iff_forall_eq _).mp ?_ ?_).symm
  exact Iff.mpr subsingleton_iff_subsingleton ‹_›

#exit

partial
def findPol (ini : Expr) : MetaM (List Expr) := do
let tName : Name := `Polynomial
dbg_trace "begin with {ini.ctorName}"
--dbg_trace ((← inferType ini).getAppFnArgs.1, (← inferType ini).ctorName)
let wini := ← if ini.ctorName == `bvar then pure ini else inferType (← whnfR ini)
--dbg_trace "about to compute int"
--let int := if ini.ctorName == `bvar then ini else ← whnf ini
dbg_trace "about to compute res {ini}, {wini}"
if ini.ctorName == `bvar then dbg_trace "went here"
let res := if ini.ctorName == `bvar then dbg_trace "went here"; [wini] else (
  if wini.isAppOf tName then [wini] else []) --| pure []
--let res := ← if (← inferType wini).isAppOf tName then pure [wini] else pure [] --| pure []
dbg_trace "computed res"
--dbg_trace res
match wini with
  | .app fn arg => do
    dbg_trace "app passage"
    dbg_trace "the body: {fn}"
--    have : sizeOf fn < sizeOf ini := sorry
--    have : sizeOf arg < sizeOf ini := sorry
    return res ++ (← findPol fn) ++ (← findPol arg)
  | .lam _na bt body _bi => do
    dbg_trace "am I ever through here now?"
--    dbg_trace f!"**  through here  **\n  '{bt} + {← ppExpr ini}'"
--    dbg_trace f!"**  through here  **\n  '{body}'"
--    have : sizeOf bt < sizeOf ini := sorry
--    have : sizeOf body < sizeOf ini := sorry
    dbg_trace f!"doing: {bt.ctorName} {body.ctorName}"
    return res ++ (← findPol bt) ++ (← findPol body)
--    dbg_trace f!"app of '{nam}'"
--    dbg_trace (← inferType tot)
    --let tail := (← myfind fn) ++ (← myfind arg)
    --let head := if ← isDefEq e fn then [fn] else []
    --let head := head ++ if ← isDefEq e arg then [tot] else []
--    return res
  | .forallE _na bt bdy _bi => do
    dbg_trace "forall passage"
--    have : sizeOf bt < sizeOf ini := sorry
--    have : sizeOf bdy < sizeOf ini := sorry
    dbg_trace f!"doing bt: {bt.ctorName}"
    let btRes := ← findPol bt
    dbg_trace f!"btRes fatto: {btRes}"
--    dbg_trace f!"{bdy.ctorName} + {← ppExpr (← inferType bdy)}"
    dbg_trace f!"doing bdy: {bdy.ctorName}"
    let bodyRes := ← findPol bdy
    dbg_trace f!"bodyRes fatto: {bodyRes}"

    let final := res ++ btRes ++ bodyRes
    dbg_trace "i go through here"
    return final
  | f => do
    dbg_trace "rest passage"
--    if (! f.ctorName == `const && (! f.ctorName == `fvar) then
--      dbg_trace (f.ctorName, ← ppExpr f, ← ppExpr (← inferType f), ← ppExpr ini)
--    dbg_trace (f); --if ← isDefEq e f then pure [f] else
--    dbg_trace (f).ctorName; --if ← isDefEq e f then pure [f] else
    pure res


irreducible_def st {R : Type _} [Ring R] (_f : R[X]) : Bool := true

example [Ring R] [Subsingleton R] : ∀ y : R[X], (X : R[X]) = y := by
  run_tac do
    let goal := ← getMainTarget
    dbg_trace (← whnfR goal).ctorName
    dbg_trace ← ppExpr goal
      dbg_trace "***  here  ***"
      let founds := ← findPol goal
      let ppfounds := ← founds.mapM (ppExpr ·)
      dbg_trace ppfounds.length
      dbg_trace f!"**  types.findPol:\n{ppfounds}"

  intros
  have : Subsingleton R[X] := Iff.mpr subsingleton_iff_subsingleton ‹_›
  have : ∀ {a b : R[X]}, a = b := by rwa [← subsingleton_iff]
  apply this

#exit

  run_tac do
    let goal := ← getMainTarget
    dbg_trace (← whnfR goal).ctorName
    dbg_trace ← ppExpr goal
      dbg_trace "***  here  ***"
      let founds := ← findPol goal
      let ppfounds := ← founds.mapM (ppExpr ·)
      dbg_trace ppfounds.length
      dbg_trace f!"**  types.findPol:\n{ppfounds}"









#check st 0

example [Ring R] (n : R) (f g : Int[X])
--  (h : f + f = 0)
--  (i : 0 * f + (f + 8) = 0)
--  (j : 0 * f + (f + 8) = 0)
--  (k : monomial 4 (5) + f = 0)
  (h : f + g = monomial 4 5 + 7)
     : ∀ y : R, if (st (monomial 10 x * (- C y) : R[X]) && st (monomial 5 (n + y))) then st (X : R[X]) else false := by
  run_tac do
    let goal := ← getMainTarget
    dbg_trace (← whnfR goal).ctorName
    dbg_trace ← ppExpr goal
--    if let some (_, lhs, rhs) := goal.eq? then
--      let pplhs := ← ppExpr lhs
--      let pptlhs := ← ppExpr (← whnf (← inferType lhs))
--      let pprhs := ← ppExpr rhs
--      let pptrhs := ← ppExpr (← inferType rhs)
--      logInfo f!"raw lhs: {pplhs}"
--      logInfo f!"typ lhs: {pptlhs}"
--      logInfo f!"raw rhs: {pprhs}"
--      logInfo f!"typ rhs: {pptrhs}"
--      dbg_trace ((← inferType rhs).getAppFnArgs.1, (← inferType rhs).ctorName)
--      let ctx  := (← getMainDecl).lctx
--      let dcls := ctx.decls.toList.reduceOption
--      let ct := ← ct.mapM (inferType ·)
--      let ct   := ← getLocalHyps
--      dbg_trace ← ct.mapM (ppExpr ·)
--      dbg_trace ← cttypes.mapM (ppExpr ·)
--      dbg_trace f!"ct.findPol:    {← ct.mapM (findPol ·)}"
--      let founds := (← ct.mapM (findPol ·)).toList.join
      dbg_trace "***  here  ***"
      let founds := ← findPol goal
      let ppfounds := ← founds.mapM (ppExpr ·)
      dbg_trace ppfounds.length
      dbg_trace f!"**  types.findPol:\n{ppfounds}"
--      let x := 0


syntax "mtc" term : tactic
#check forallTelescope
open Elab Term in
elab_rules : tactic
| `(tactic| mtc $stx:term) => withMainContext do
  let estx := ← Term.elabTerm stx none
  let ctx  := (← getMainDecl).lctx
  let dcls := ctx.decls.toList.reduceOption
  let ct   := ← getLocalHyps
  dbg_trace f!"hyps:   {← ct.mapM (ppExpr ·)}"
  dbg_trace f!"hyps:   {← ct.mapM fun d => do let dt := ← inferType d; (ppExpr dt)}"
  let hypsTypes := ← ct.mapM (inferType ·)
  dbg_trace f!"hypsF:  {← hypsTypes.mapM (ppExpr ·)}"
  let found := ← hypsTypes.mapM (myfind estx ·)
  dbg_trace f!"found: {← found.toList.join.mapM (ppExpr ·)}"
  dbg_trace ← (dcls.mapM fun d => ppExpr d.type)
  let decs := ← forallTelescope (← getMainDecl).type (fun arr _k => pure arr)
  dbg_trace (← getMainDecl).type
  dbg_trace f!"decs: {decs}"
  let cands := ← ff estx ct.toList --(dcls.map (LocalDecl.type ·))
  dbg_trace ← cands.mapM (ppExpr ·)
#check SubExpr
#check Lean.Meta.find

theorem hi (a b : Nat) (h₁ : a + b = 5) (h₂ : a + b + 4 = 5) : True := by
  intros
  mtc a + _
  run_tac do
    let ctx := ← getLCtx
    let dcls := ctx.decls.toList.reduceOption



#exit
  run_tac do
    let g ← getMainTarget
    let (is_natDeg, pol) := ← isDegLE g
    let nextp := ← ppExpr (← mkNatDegreeLE pol false)
    logInfo nextp
--    let dcls := (←getLCtx).decls
    addNatDegreeDecl { raw := mkAtom "oy" } pol is_natDeg
    let _ := ← evalTactic (← `(tactic| refine LE.le.trans ‹_› ?_))
    withMainContext do
      let last := (← getLCtx).lastDecl
--      dbg_trace last.get!.userName
--      let pp := (← getLCtx).pop

      --dbg_trace (← getLCtx).decls.toList.reduceOption.map (LocalDecl.userName ·)
      --dbg_trace last.get!.userName
      --dbg_trace pp.decls.toList.reduceOption.map (LocalDecl.userName ·)
      let new := ← (← getMainGoal).clear last.get!.fvarId
--      let j := ← getUnsolvedGoals
      setGoals [new]
  norm_num
  --clear this
#exit
    withMainContext do
--    let dcls1 := (←getLCtx).decls
--    let d := dcls1.toList.reduceOption.find? fun x =>
--      ! ((dcls.toList.reduceOption.map (LocalDecl.toExpr ·)).contains x.toExpr)
    --dbg_trace d.get!.userName
    let guessDegree := ← toNatDegree (fun p => dbg_trace p.getAppFnArgs; mkAppM ``natDegree #[p] <|>
      return mkNatLit 0) pol
    let gds := ← guessDegree.toSyntax
    let _ := ← evalTactic (← `(tactic| refine LE.le.trans (b := $gds) ?_ ?_))
    focusAndDone (← getMainGoal).assumption
/-

    let newGoal := ← (← getMainGoal).clear d.get!.fvarId
--    setGoals (← getGoals)
    setGoals [newGoal]
--/
  --evalTactic (← `(tactic| refine degree_le_natDegree.trans ?_; refine Nat.cast_le.mpr ?_)) <|>
  --  pure ()
  have := degree_le_natDegree.trans (Nat.cast_le.mpr this)
  --refine this.trans ?_
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


example (a : Int) (b : Nat) (hb : b ≤ 2) : natDegree (((3 * a : Int) : Int[X]) + ((X + C a * X + monomial 3 9) * X ^ b) ^ 2) ≤ 10 := by
  run_tac do
    let g ← getMainTarget
    let (is_natDeg, pol, _) := ← isDegLE g
    let nEQ := ← mkNatDegreeLE pol is_natDeg
    let _ := ← instantiateMVars nEQ
    let nEQS := ← nEQ.toSyntax
    let ns : TSyntax `Mathlib.Tactic.optBinderIdent := { raw := mkAtom "" }
    let dcls := (←getLCtx).decls
    let (mv1, mv2) := ← haveLetCore (← getMainGoal) ns #[] (some nEQS) true
    setGoals [mv1]
    focusAndDone <| CDL pol
    setGoals [mv2]
    withMainContext do
    let dcls1 := (←getLCtx).decls
    let d := dcls1.toList.reduceOption.find? fun x =>
      ! ((dcls.toList.reduceOption.map (LocalDecl.toExpr ·)).contains x.toExpr)
    dbg_trace d.get!.userName
    let guessDegree := ← toNatDegree (fun p => dbg_trace p.getAppFnArgs; mkAppM ``natDegree #[p] <|> return mkNatLit 0) pol
    let gds := ← guessDegree.toSyntax
    let _ := ← evalTactic (← `(tactic| refine LE.le.trans (b := $gds) ‹_› ?_))
    let newGoal := ← (← getMainGoal).clear d.get!.fvarId
    setGoals [newGoal]
  --assumption
  --refine this.trans ?_
  --clear this
  --linarith [hb]
  show _ ≤ 2 * (3 + 2)
  simp
  assumption



#exit

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
