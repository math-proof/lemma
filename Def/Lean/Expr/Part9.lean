import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Inductive.Lean.Expr.Part4
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def Expr.priority : Expr → Nat
  | nil => 0
  | sort ..
  | const _ => 2048
  | Symbol .. => 2048
  | Basic (.ExprWithAttr (.Lean_operatorname `id)) [e] _ => e.priority
  | Basic op ..  => op.priority
  | Binder binder .. => binder.func.priority

def Expr.level : Expr → Nat
  | Basic op _ level  => level
  | _ => 0

def Expr.isEmpty : Expr → Bool
  | nil => true
  | _ => false

/-- Shape argument of `Tensor α s`, if this node is that type. -/
def Expr.tensorShape? : Expr → Option Expr
  | Basic (.ExprWithAttr (.Lean_typeclass `Tensor)) args _ =>
    match args with
    | [_, shape] => some shape
    | [shape] => some shape
    | _ => none
  | _ => none


def Expr.isTypeClass : Expr → Bool
  | Basic (.ExprWithLimits .Lean_forall) (.sort .zero :: _) _ => true
  | _ => false


def getExprMVarAssignment (mvarId : Lean.MVarId) : MetaM Lean.Expr := do
    if let some e ← Lean.getExprMVarAssignment? mvarId then
      return e
    if let some dAssign ← Lean.getDelayedMVarAssignment? mvarId then
      if let some e' ← Lean.getExprMVarAssignment? dAssign.mvarIdPending then
        let mdecl := (← getMCtx).getDecl dAssign.mvarIdPending
        return ← withLCtx mdecl.lctx mdecl.localInstances do
          let mut e := e'
          let mut binderName := #[]
          let mut binderType := #[]
          for (i, fvar) in dAssign.fvars.mapIdx Prod.mk do
            if let .fvar fvarId := fvar then
              e ← e.subs fvarId i
              let name ←
                if let some decl ← fvarId.findDecl? then
                  pure decl.userName
                else
                  panic! s!"Expr.func.fvar : unknown free variable {fvarId.name}"
              binderName := binderName.push name
              binderType := binderType.push (← inferType fvar)

          return Array.zip binderName binderType |>.foldl (init := e) fun e (name, type) =>
            .lam name type e .implicit
    return .const `«?» []


def «?» := 0


