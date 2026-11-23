module

public import Def.Lean.Expr.Part11

@[expose] public section

set_option linter.unusedVariables false


def LimTo.latex : LimTo → String
  | inf => "\\infty"
  | ninf => "-\\infty"
  | nhds _ | nhdsPos _ | nhdsNeg _ => ""
