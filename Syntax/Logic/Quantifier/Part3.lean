module

public meta import Lean
public import Syntax.Logic.Quantifier.Part2

public meta section

open Lean (Macro explicitBinders)


syntax "∃" explicitBinders "|" term ", " term : term



macro_rules
  | `(∃ $x | $cond, $body) => `(∃ $x, $cond ∧ $body)
