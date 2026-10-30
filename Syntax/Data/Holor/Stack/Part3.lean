import Instance.Data.Holor.Tensor.Part2
import Syntax.Data.Holor.Stack.Part2
open Lean


/--
Tensor product along axis 0 of a stack: `∏ i < n, f i` means `([i < n] f i).prod 0`.
Uses priority above Mathlib's bounded `∏ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∏ " binderIdent "<" term ", " term:67 : term



macro_rules
  | `(∏ _ < $n, $body) => `(([ _ < $n ] $body).prod 0)
  | `(∏ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).prod 0)
