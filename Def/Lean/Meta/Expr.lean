import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


def Lean.Expr.is_Prop (e : Expr) : MetaM Bool := do
  match e with
  | .app e_fn _ =>
    -- HasEquiv.Equiv / Setoid approx: inferType yields a forall
    -- ending in Prop whose Sort is an assigned universe mvar;
    -- body.isProp / u.isZero is false until instantiateMVars
    -- (prints as Prop/0 but is not concrete .zero).
    if let .forallE _ _ body _ ← instantiateMVars (← inferType e_fn) then
      return body.isProp

  | .forallE (body := body) .. =>
    return ← body.is_Prop

  | .fvar fvarId =>
    if let some decl ← fvarId.findDecl? then
      return (← instantiateMVars decl.type).isProp

  | _  =>
    pure ()

  return false

