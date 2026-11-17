module

public meta import Lean
public import Syntax.Logic.Quantifier.Part3

public meta section

open Lean (Macro explicitBinders)


syntax "∃" explicitBinders "∈" term "|" term ", " term : term



macro_rules
  | `(∃ $x ∈ $domain | $cond, $body) => do
    let `(explicitBinders| $xIdent:ident) := x | Macro.throwError "expected explicit binders"
    `(∃ $x, $xIdent ∈ $domain ∧ $cond ∧ $body)
