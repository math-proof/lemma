module

public import Def.Lean.PrettyPrinter.Latex.Nat
public import Def.Lean.PrettyPrinter.Latex.Expr.Basic

@[expose] public section

open Lean (Name)
set_option linter.unusedVariables false


def BinaryInfix.latexFormat (op : BinaryInfix) (left right : Expr) (level : ℕ)
    (command : Option String := none) : String :=
  let func := op.func
  let opStr := command.getD func.command
  -- (`toColor ignore`: `true` drops the parentheses) a tuple keeps its parentheses; so does a lambda on the
  -- left, whose body would otherwise swallow the operator (`(fun x ↦ x t) = …`).
  -- A fraction (`HDiv` / `Div` / `Rat.divInt`) is one TeX atom (`\frac`). Lean still parenthesizes it
  -- on the left of a tighter operator (`(a / b) • v`, priorities 70 < 73); those parentheses are omitted.
  -- The right operand already drops them via `is_Div`.
  let left := level.toColor ((left.priority ≥ func.priority || left.is_EnclosedGroup || left.is_Div) && !left.is_JointRandomSymbol && !left.is_Lambda)
  let right := level.toColor ((right.priority > func.priority || right.is_Div || right.is_BlockMatrix) && !right.is_JointRandomSymbol)
  s!"{left} {opStr} {right}"
