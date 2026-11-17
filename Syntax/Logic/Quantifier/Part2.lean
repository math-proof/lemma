module

public meta import Lean
public import Syntax.Logic.Quantifier

public meta section

open Lean (Macro explicitBinders)


syntax "∀" ident "∈" term "|" term ", " term : term



macro_rules
  | `(∀ $x ∈ $domain | $cond, $body) => `(∀ $x, $x ∈ $domain → $cond → $body)
