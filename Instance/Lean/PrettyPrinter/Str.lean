import Def.Lean.Expr.Part11
import Def.Lean.Level
import Def.Lean.PrettyPrinter.Str
open Lean (FVarId Name)


instance : ToString Expr where
  toString := Expr.toString

instance : ToString Operator where
  toString : Operator → String
  | op => op.operator

instance : ToString FVarId where
  toString : FVarId → String
  | id => id.name.toString

