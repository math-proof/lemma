import Instance.Data.Holor.Tensor.Part2
import Syntax.Data.Holor.Stack
open Lean


macro_rules
  | `([_ < $n] $body) => `(Stack $n fun _ => $body)
  | `([$x:ident < $n] $body) => `(Stack $n fun $x => $body)

