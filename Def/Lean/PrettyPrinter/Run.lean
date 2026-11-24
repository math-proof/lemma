module
public import Def.Lean.PrettyPrinter.Json
public import Def.Lean.Io
public import Mathlib


public section

-- lake env lean --run Def/Lean/PrettyPrinter/Run.lean add_mul
-- lake env lean Def/Lean/PrettyPrinter/Run.lean

def main (args : List String) : IO Unit := do
  IO.println <| ← Name.toJson args.head!.toName |> exec

#eval do
  let name := `Matrix.mul_apply
  let expr ← name.toExpr
  println! ← Lean.Meta.ppExpr expr
  let expr ← Expr.toExpr expr [] 0
  println! expr
  println! expr.toLatex
  -- println! ← Name.toJson name

