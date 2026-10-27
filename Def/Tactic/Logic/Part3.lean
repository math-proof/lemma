import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import Def.Lean.Meta.Expr.Part4 -- using Lean.Expr.is_Prop
import Def.Lean.FVarId
import Syntax.Tactic.Logic.Part2
open Lean Elab.Tactic Meta Parser.Tactic


@[tactic mpr]
def evalMpr : Tactic
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


