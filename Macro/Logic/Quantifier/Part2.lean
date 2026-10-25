import Lean
import Syntax.Logic.Quantifier.Part2
open Lean (Macro explicitBinders)


macro_rules
  | `(∀ $x ∈ $domain | $cond, $body) => `(∀ $x, $x ∈ $domain → $cond → $body)


