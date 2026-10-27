import Def.Lean.Name
import Def.Lean.BinderInfo.Part2
import Def.Lean.Meta.Expr.Part2
open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


instance : ToString Binder where
  toString := Binder.toString


