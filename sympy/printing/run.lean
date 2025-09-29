-- lake env lean --run sympy/printing/run.lean add_mul
-- lake env lean sympy/printing/run.lean
import sympy.printing.json
import sympy.io
import Mathlib

#eval do
  let name := `Matrix.mul_apply
  let expr ← name.toExpr
  println! ← Lean.Meta.ppExpr expr
  let expr ← Expr.toExpr expr []
  println! expr
  println! expr.toLatex
  -- println! ← Name.toJson name

def main (args : List String) : IO Unit := do
  IO.println <| ← Name.toJson args.head!.toName |> exec

#check CommGrp.forget_commGrp_preserves_epi
