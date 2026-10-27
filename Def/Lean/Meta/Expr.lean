import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


def Lean.Expr.is_Prop (e : Expr) : MetaM Bool := do
  match e with
  | .app e_fn _ =>
    if let .forallE _ _ body _ ← inferType e_fn then
      return body.isProp

  | .forallE (body := body) .. =>
    return ← body.is_Prop

  | .fvar fvarId =>
    if let some decl ← fvarId.findDecl? then
      return decl.type.isProp

  | _  =>
    pure ()

  return false


