import Lean
import Syntax.Logic.Quantifier
open Lean (Macro explicitBinders)


macro_rules
  | `(∀ $x | $cond, $body) => `(∀ $x, $cond → $body)


