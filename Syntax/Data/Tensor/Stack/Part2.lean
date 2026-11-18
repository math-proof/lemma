module

public meta import Lean
public import Instance.Data.Tensor.Tensor.Part2
public import Syntax.Data.Tensor.Stack

public meta section

open Lean


/--
Tensor sum along axis 0 of a stack: `∑ i < n, f i` means `([i < n] f i).sum 0`.
Uses priority above Mathlib's bounded `∑ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∑ " binderIdent "<" term ", " term:67 : term



macro_rules
  | `(∑ _ < $n, $body) => `(([ _ < $n ] $body).sum 0)
  | `(∑ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).sum 0)
