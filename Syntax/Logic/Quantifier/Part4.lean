import Lean
import Syntax.Logic.Quantifier.Part3
open Lean (Macro explicitBinders)


syntax "∃" explicitBinders "∈" term "|" term ", " term : term



macro_rules
  | `(∃ $x ∈ $domain | $cond, $body) => do
    let `(explicitBinders| $xIdent:ident) := x | Macro.throwError "expected explicit binders"
    `(∃ $x, $xIdent ∈ $domain ∧ $cond ∧ $body)
