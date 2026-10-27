import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
import Inductive.Lean.Meta.Expr
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


def Binder.toString : Binder → String := CtorName.ctorName


