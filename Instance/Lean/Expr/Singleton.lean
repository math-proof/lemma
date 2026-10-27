import Def.Lean.Name
import Mathlib.Basic.Real.Basic
import Def.Lean.Expr.Singleton
open Lean


instance : ToString Constant where
  toString := Constant.toString


