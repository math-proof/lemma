import Lean
import Syntax.Logic.Quantifier
open Lean (Macro explicitBinders)


syntax "∀" ident "∈" term "|" term ", " term : term



macro_rules
  | `(∀ $x ∈ $domain | $cond, $body) => `(∀ $x, $x ∈ $domain → $cond → $body)
