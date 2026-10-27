import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Inductive.Lean.Expr.Part6
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


/-- `true` = `atTop` (`∞`), `false` = `atBot` (`-∞`). -/
def Expr.asAtTopBot? : Expr → Option Bool
  | Basic (.ExprWithAttr op) _ _ =>
    match op.name.getLast with
    | `atTop => some true
    | `atBot => some false
    | _ => none
  | const (.ident name) =>
    match name.getLast with
    | `atTop => some true
    | `atBot => some false
    | _ => none
  | _ => none

def Expr.asSingleton? : Expr → Option Expr
  | Basic (.Special ⟨`Singleton.singleton⟩) [x] _ => some x
  | Basic func [x] _ =>
    if func.name.getLast == `singleton then some x else none
  | _ =>
    none

def Expr.isComplOfSingleton (s pt : Expr) : Bool :=
  match s with
  | Basic func args _ =>
    let isCompl :=
      match func.name.getLast with
      | `compl | `complement => true
      | _ => false
    isCompl &&
      match args with
      | [t] => t.asSingleton? == some pt
      | [a, b] => a.asSingleton? == some pt || b.asSingleton? == some pt
      | _ => false
  | _ =>
    false

/-- `nhdsWithin x (Ioi x)` / `nhdsWithin x (Iio x)`. -/
def Expr.asNhdsWithinOneSided? : Expr → Option LimTo
  | Basic func [x, s] _ =>
    if func.name.getLast == `nhdsWithin then
      match s with
      | Basic sfunc [a] _ =>
        if a == x then
          match sfunc.name.getLast with
          | `Ioi => some (.nhdsPos x)
          | `Iio => some (.nhdsNeg x)
          | _ => none
        else
          none
      | _ =>
        none
    else
      none
  | _ =>
    none

/-- `nhdsWithin x₀ {x₀}ᶜ` for a general point (including `0`). -/
def Expr.asNhdsWithinPunctured? : Expr → Option Expr
  | Basic func [x, s] _ =>
    if func.name.getLast == `nhdsWithin && s.isComplOfSingleton x then some x
    else none
  | _ =>
    none

/-- `f.map fun n => e` with `f` = `atTop` / `atBot`. -/
def Expr.asMapAtTopBotLambda? : Expr → Option (Name × LimTo × Expr)
  | Basic func args _ =>
    let pair? : Option (Expr × Expr) :=
      match func, args with
      | .ExprWithAttr (.LeanMethod `Filter.map _), [fn, filt]
      | .ExprWithAttr (.Lean_operatorname `Filter.map), [fn, filt]
      | .ExprWithAttr (.Lean_function `Filter.map), [fn, filt]
      | .BinaryInfix ⟨`Functor.map⟩, [fn, filt] =>
        some (fn, filt)
      | .ExprWithAttr (.LeanMethod name _), [fn, filt] =>
        if name.getLast == `map then some (fn, filt) else none
      | _, _ =>
        none
    match pair? with
    | some (Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default n _ _] _, filt) =>
      filt.asAtTopBot?.map fun isTop => (n, if isTop then .inf else .ninf, fn)
    | _ =>
      none
  | _ =>
    none

/--
`limUnder atTop/atBot/nhdsWithin (fun n => e)`.
Returns binder name, limit direction, and the body.
-/
def Expr.asLimBound? : List Expr → Option (Name × LimTo × Expr)
  | [filt, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default n _ _] _] =>
    match filt.asAtTopBot? with
    | some true => some (n, .inf, fn)
    | some false => some (n, .ninf, fn)
    | none =>
      (filt.asNhdsWithinOneSided?.map fun dir => (n, dir, fn)) <|>
        (filt.asNhdsWithinPunctured?.map fun x => (n, LimTo.nhds x, fn))
  | [mapped] =>
    mapped.asMapAtTopBotLambda?
  | _ =>
    none

