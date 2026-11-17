module

public import Def.Lean.Expr.Part11
public import Def.Lean.Level
public import Def.Lean.PrettyPrinter.Str

@[expose] public section

open Lean (FVarId Name)


instance : ToString Expr where
  toString := Expr.toString

instance : ToString Operator where
  toString : Operator → String
  | op => op.operator

instance : ToString FVarId where
  toString : FVarId → String
  | id => id.name.toString

