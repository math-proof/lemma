module

public meta import Lean

public meta section

open Lean (Macro explicitBinders)


syntax "∀" ident "|" term ", " term : term



macro_rules
  | `(∀ $x | $cond, $body) => `(∀ $x, $cond → $body)
