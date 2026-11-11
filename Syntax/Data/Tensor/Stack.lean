import Instance.Data.Tensor.Tensor.Part2
import Def.Data.Tensor.Stack
open Lean


/-!
Tensor stack sugar `[i < n] body` → `Stack n fun i => body`.

Unscoped so Tensor lemmas get it by importing this module (transitively).
Matrix one-index row sugar uses the same surface form under `open scoped Matrix`
(`Syntax.LinearAlgebra.Matrix.Notation`); keep those scopes apart in one file.
-/

syntax "[" binderIdent "<" term "]" term:67 : term



macro_rules
  | `([_ < $n] $body) => `(Stack $n fun _ => $body)
  | `([$x:ident < $n] $body) => `(Stack $n fun $x => $body)
