module

public meta import Lean
public import Instance.Data.Tensor.Tensor
public import Def.Data.Tensor.Stack

public meta section

open Lean


/-!
Tensor stack sugar.

* `[i < n] body` → `Stack n fun i => body`.
* `∑ i < n, f i` → `([i < n] f i).sum 0` (priority above Mathlib's bounded `∑`).
* `∏ i < n, f i` → `([i < n] f i).prod 0` (priority above Mathlib's bounded `∏`).

Unscoped so Tensor lemmas get it by importing this module (transitively).
Matrix one-index row sugar uses the same surface form under `open scoped Matrix`
(`Syntax.LinearAlgebra.Matrix.Notation`); keep those scopes apart in one file.
-/

syntax "[" binderIdent "<" term "]" term:67 : term



macro_rules
  | `([_ < $n] $body) => `(Stack $n fun _ => $body)
  | `([$x:ident < $n] $body) => `(Stack $n fun $x => $body)

/--
Tensor sum along axis 0 of a stack: `∑ i < n, f i` means `([i < n] f i).sum 0`.
Uses priority above Mathlib's bounded `∑ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∑ " binderIdent "<" term ", " term:67 : term



macro_rules
  | `(∑ _ < $n, $body) => `(([ _ < $n ] $body).sum 0)
  | `(∑ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).sum 0)

/--
Tensor product along axis 0 of a stack: `∏ i < n, f i` means `([i < n] f i).prod 0`.
Uses priority above Mathlib's bounded `∏ i < n, …` (Finset.Iio) notation.
-/
syntax (priority := 10000) "∏ " binderIdent "<" term ", " term:67 : term



macro_rules
  | `(∏ _ < $n, $body) => `(([ _ < $n ] $body).prod 0)
  | `(∏ $x:ident < $n, $body) => `(([ $x:ident < $n ] $body).prod 0)
