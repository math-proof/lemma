import Initialize.Lean.Meta.CtorName
import Def.Lean.BinderInfo


instance : ToString Lean.BinderInfo where
  toString := ctorName

