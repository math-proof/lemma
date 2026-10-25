import Lean
import Syntax.Logic.Quantifier.Part4
open Lean (Macro explicitBinders)


macro_rules
  | `(∃ $x ∈ $domain | $cond, $body) => do
    let `(explicitBinders| $xIdent:ident) := x | Macro.throwError "expected explicit binders"
    `(∃ $x, $xIdent ∈ $domain ∧ $cond ∧ $body)

