import Theorem.LinearAlgebra.Matrix.OfFun
open Lean


/-!
# Matrix entry notation (Fin-indexed)

Mirrors `Mathlib.LinearAlgebra.Matrix.Notation` under `Syntax/`.
Mathlib's `!![…]` stays the literal grid. This file adds the functional form.

- Two-index (always available): `[i < m, j < n] f i j` → `Matrix.ofFun m n fun i j => f i j`
- One-index (`open scoped Matrix`): `[i < n] row` → `Matrix.of fun (i : Fin n) => row`,
  i.e. a matrix whose `i`-th row is `row` (typically `Fin d → α`).

The one-index form is `scoped` in namespace `Matrix` so it does not fight Tensor stack sugar
`[i < n] body` from `Syntax.Data.Tensor.Stack` (unscoped). Prefer not to
`open scoped Matrix` in the same file that also imports the Tensor stack syntax.
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

namespace Matrix

/--
`[i < n] body` → matrix whose `i`-th row is `body`.

Example (needs `open scoped Matrix`):
`θ = [i < n] ((i : ℝ) • τ)` elaborates at expected type `ℝ ^ [n, d]`.
-/
scoped syntax (name := matrixOfRows) "[" binderIdent "<" term "]" term:67 : term

macro_rules (kind := matrixOfRows)
  | `([_ < $n] $body) => `(Matrix.of (fun (_ : Fin $n) => $body))
  | `([$i:ident < $n] $body) => `(Matrix.of (fun ($i : Fin $n) => $body))

end Matrix
