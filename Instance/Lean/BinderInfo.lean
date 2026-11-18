module

public import Initialize.Lean.Meta.CtorName
public import Def.Lean.BinderInfo

@[expose] public section

instance : ToString Lean.BinderInfo where
  toString := ctorName

