module

public import Mathlib.Tactic
public import Theorem.Bool.Or.of.Or.Imp
public import Theorem.Bool.And.of.And.Imp
public import Theorem.Bool.Imp.is.ImpNotS
public import Theorem.Bool.Imp.of.Imp.Imp
public import Def.Lean.Meta.Expr -- using Lean.Expr.is_Prop
public import Def.Lean.FVarId
public meta import Def.Tactic.Logic
public import Syntax.Tactic.Logic.Part2

@[expose] public section

open Lean Elab.Tactic Meta Parser.Tactic


@[tactic mpr]
meta def evalMpr : Tactic
| `(tactic| mpr [ $[ $h₀ ],* ] $[$loc:location]?) => employModusPonens `mpr h₀ loc true
| _ => throwError "Usage: mpr [ <term>,+ ] at <location>?"


def Eq.left {a b : α} (_ : a = b) : α := a

def Eq.right {a b : α} (_ : a = b) : α := b


def evalLet (t : Ident) (e : Expr) : TacticM Unit := do
  let e ← PrettyPrinter.delab e
  evalTactic (← `(tactic| let $t := $e))

def evalHave (h_t : Ident) (t : Ident) (e : Expr) (reverse : Bool) : TacticM Unit := do
  let e ← PrettyPrinter.delab e
  let eq ← if reverse then `($e = $t) else `($t = $e)
  evalTactic (← `(tactic| have $h_t : $eq := rfl))

def letAssignment (h_t : Ident) (t : Ident) (reverse : Bool) : TacticM Unit := do
  let mainGoal ← getMainGoal
  let (fvarId, mainGoal) ← mainGoal.intro t.getId
  replaceMainGoal [mainGoal]
  mainGoal.withContext do
    let some decl ← fvarId.findDecl? | throwError "denote: failed to find the declaration from `let statement "
    let some e := decl.value? | throwError "denote: failed to find the value from the `let statement"
    evalHave h_t t e reverse


def haveDeclaration (h_t : Ident) (t : Ident) (e : Expr) (reverse : Bool) : TacticM Unit := do
  let e :=
    match e with
    | .app (.app (.app (.app (.const ``Eq.right _) _) _) rhs) _ => rhs
    | .app (.app (.app (.app (.const ``Eq.left _) _) lhs) _) _ => lhs
    | e => e
  evalLet t e
  evalHave h_t t e reverse


