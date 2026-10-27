import Instance.Data.Holor.Tensor.Part2
import Syntax.Data.Holor.Stack.Part3
open Lean


macro_rules
  | `(∏ _ < $n, $body) => `(([ _ < $n ] $body).prod 0)
  | `(∏ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).prod 0)


