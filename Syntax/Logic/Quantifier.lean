import Lean
open Lean (Macro explicitBinders)


syntax "∀" ident "|" term ", " term : term



macro_rules
  | `(∀ $x | $cond, $body) => `(∀ $x, $cond → $body)
