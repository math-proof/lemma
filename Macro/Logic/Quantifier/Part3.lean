import Lean
import Syntax.Logic.Quantifier.Part3
open Lean (Macro explicitBinders)


macro_rules
  | `(∃ $x | $cond, $body) => `(∃ $x, $cond ∧ $body)


