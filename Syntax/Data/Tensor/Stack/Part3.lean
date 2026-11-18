module

public meta import Lean
public import Instance.Data.Tensor.Tensor.Part2
public import Syntax.Data.Tensor.Stack.Part2

public meta section

open Lean


/--
Tensor product along axis 0 of a stack: `∏ i < n, f i` means `([i < n] f i).prod 0`.
Uses priority above Mathlib's bounded `∏ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∏ " binderIdent "<" term ", " term:67 : term



macro_rules
  | `(∏ _ < $n, $body) => `(([ _ < $n ] $body).prod 0)
  | `(∏ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).prod 0)
