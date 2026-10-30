import Instance.Data.Holor.Tensor.Part2
import Def.Data.Holor.Stack
open Lean


syntax "[" binderIdent "<" term "]" term:67 : term



macro_rules
  | `([_ < $n] $body) => `(Stack $n fun _ => $body)
  | `([$x:ident < $n] $body) => `(Stack $n fun $x => $body)
