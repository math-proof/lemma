/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SpiveyPQBell.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.SpiveyPQBell.Part9
/-!
# The `(p, q)`-deformed Spivey formula

This file proves Oussi's addition formula for the `(p, q)`-Bell numbers.  The proof uses
the operator calculus of the source, interpreted on formal power series so that no analytic
convergence argument is needed.
-/


namespace MetaMathlibExt

open scoped BigOperators

def spivey_finish_public : Lean.Elab.Tactic.TacticM Unit := do
  let goal ← Lean.Elab.Tactic.getMainGoal
  goal.withContext do
    let target ← Lean.instantiateMVars (← goal.getType)
    let recs ← Lean.Elab.Term.getLetRecsToLift
    let mut rec? := none
    for mvarId in (← Lean.Meta.getMVars target) do
      let root ← Lean.getDelayedMVarRoot mvarId
      if let some rec := recs.find? (fun rec => rec.mvarId == root) then
        rec? := some rec
    let some rec := rec? | throwError "recursive declaration `S` not found"
    let lctx ← Lean.getLCtx
    let getLocal (name : Lean.Name) : Lean.Meta.MetaM Lean.Expr := do
      let some decl := lctx.findFromUserName? name | throwError "local `{name}` not found"
      return decl.toExpr
    let p ← getLocal `p
    let q ← getLocal `q
    let bracket ← getLocal `bracket
    let hbracket0 ← getLocal `hbracket0
    let hbracketAdd ← getLocal `hbracketAdd
    let hbracket_ne ← getLocal `hbracket_ne
    let m ← getLocal `m
    let n ← getLocal `n
    let S := Lean.mkAppN (.const rec.declName []) #[p, q, bracket]
    let generic := Lean.mkConst ``spivey_generic_sum
    let mut genericType ← Lean.Meta.inferType generic
    for arg in #[p, q, bracket, S, hbracket0, hbracketAdd, hbracket_ne] do
      genericType := genericType.bindingBody!.instantiate1 arg
    let hS0Type := genericType.bindingDomain!
    let hS0 ← Lean.Meta.forallTelescopeReducing hS0Type fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "initial equation expected"
      let refl ← Lean.Meta.mkAppM ``Eq.refl #[rhs]
      Lean.Meta.mkLambdaFVars xs refl
    genericType := genericType.bindingBody!.instantiate1 hS0
    let hSsucc0Type := genericType.bindingDomain!
    let (hSsucc0, realZero) ← Lean.Meta.forallTelescopeReducing hSsucc0Type fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "zero equation expected"
      let refl ← Lean.Meta.mkAppM ``Eq.refl #[rhs]
      return (← Lean.Meta.mkLambdaFVars xs refl, rhs)
    genericType := genericType.bindingBody!.instantiate1 hSsucc0
    let hSsuccType := genericType.bindingDomain!
    let hSsucc ← Lean.Meta.forallTelescopeReducing hSsuccType fun xs body => do
      let some (_, _, rhs) := body.eq? | throwError "successor equation expected"
      let k := xs[1]!
      let hk := xs[2]!
      let natZero := Lean.mkNatLit 0
      let hne ← Lean.Meta.mkAppM ``Nat.ne_of_gt #[hk]
      let condition := Lean.mkAppN (Lean.mkConst ``Eq [.succ .zero])
        #[Lean.mkConst ``Nat, k, natZero]
      let decision := Lean.mkApp2 (Lean.mkConst ``Nat.decEq) k natZero
      let proof := Lean.mkAppN (Lean.mkConst ``if_neg [.succ .zero])
        #[condition, decision, hne, Lean.mkConst ``Real, realZero, rhs]
      Lean.Meta.mkLambdaFVars xs proof
    let proof := Lean.mkAppN generic
      #[p, q, bracket, S, hbracket0, hbracketAdd, hbracket_ne,
        hS0, hSsucc0, hSsucc, m, n]
    goal.assign proof
    Lean.Elab.Tactic.replaceMainGoal []

end MetaMathlibExt
