module

public import Def.Lean.Name
public import Def.Lean.BinderInfo
public import Def.Lean.Meta.Expr.Part2

@[expose] public section

open Lean.Meta
open Lean (BinderInfo PPContext FormatWithInfos Expr Core.Context getEnv getMCtx getLCtx getOptions ppExt)


instance : ToString Binder where
  toString := Binder.toString


