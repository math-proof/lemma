import Instance.Data.Holor.Tensor.Part2
import Syntax.Data.Holor.Stack.Part2
open Lean


macro_rules
  | `(∑ _ < $n, $body) => `(([ _ < $n ] $body).sum 0)
  | `(∑ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).sum 0)

