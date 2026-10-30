import Lean
import Syntax.Logic.Quantifier.Part2
open Lean (Macro explicitBinders)


syntax "∃" explicitBinders "|" term ", " term : term



macro_rules
  | `(∃ $x | $cond, $body) => `(∃ $x, $cond ∧ $body)
