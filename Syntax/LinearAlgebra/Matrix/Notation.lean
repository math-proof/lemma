import sympy.matrices.ofFun
open Lean


/-!
# Matrix entry notation (Fin-indexed)

Mirrors `Mathlib.LinearAlgebra.Matrix.Notation` under `Syntax/`.
Mathlib's `!![…]` stays the literal grid. This file adds the functional form.

Distinct from Tensor stack sugar `[i < n] body` (`torch/stack.lean`): the comma form is Matrix-only.

`[i < m, j < n] f i j` elaborates to `Matrix.ofFun m n fun i j => f i j`,
which is definitionally `Matrix.of fun (i : Fin m) (j : Fin n) => …`.
-/

/--
`[i < m, j < n] body` → `Matrix.ofFun m n fun i j => body`.

Square case: `[i < n, j < n] …`.
-/
syntax "[" binderIdent "<" term ", " binderIdent "<" term "]" term:67 : term

macro_rules
  | `([_ < $m, _ < $n] $body) => `(Matrix.ofFun $m $n fun _ _ => $body)
  | `([$i:ident < $m, _ < $n] $body) => `(Matrix.ofFun $m $n fun $i _ => $body)
  | `([_ < $m, $j:ident < $n] $body) => `(Matrix.ofFun $m $n fun _ $j => $body)
  | `([$i:ident < $m, $j:ident < $n] $body) =>
    `(Matrix.ofFun $m $n fun $i $j => $body)

/-- Infoview: print `Matrix.ofFun m n fun i j => …` as `[i < m, j < n] …`. -/
@[app_unexpander Matrix.ofFun]
def Matrix.ofFun.unexpand : PrettyPrinter.Unexpander
  | `($_ $m:term $n:term fun $i:ident $j:ident => $body) =>
    `([$i:ident < $m, $j:ident < $n] $body)
  | `($_ $m:term $n:term fun $i:ident _ => $body) =>
    `([$i:ident < $m, _ < $n] $body)
  | `($_ $m:term $n:term fun _ $j:ident => $body) =>
    `([_ < $m, $j:ident < $n] $body)
  | `($_ $m:term $n:term fun _ _ => $body) =>
    `([_ < $m, _ < $n] $body)
  | _ =>
    throw ()
