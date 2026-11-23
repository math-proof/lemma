module

public meta import Lean
public import Theorem.LinearAlgebra.Matrix.OfFun

public meta section

open Lean


/-!
# Matrix entry notation (Fin-indexed)

Mirrors `Mathlib.LinearAlgebra.Matrix.Notation` under `Syntax/`.
Mathlib's `!![…]` stays the literal grid. This file adds the functional form.

- One-index (`open scoped Matrix`): `[i < n] body`.
  If `body` is a row (`Fin d → α`), this is `Matrix.of fun (i : Fin n) => body`; if
  `body` is an entry, it is the vector `fun (i : Fin n) => body : Fin n → α`.
  Groups stack, so `[i < m][j < n] f i j` is the 2-D matrix `Matrix.ofFun m n f`
  (equivalently `[j < n][i < m] f i j` is its transpose).

The syntax is `scoped` in namespace `Matrix` so it does not fight Tensor stack sugar
`[i < n] body` from `Syntax.Data.Tensor.Stack` (unscoped). Prefer not to
`open scoped Matrix` in the same file that also imports the Tensor stack syntax.
-/

namespace Matrix

/--
`[i < n] body` → `Matrix.of (fun (i : Fin n) => body)` when `body` is a row
(`Fin d → α`), otherwise the vector `fun (i : Fin n) => body : Fin n → α`.

Keeping the `Matrix.of` head for rows preserves the `Matrix` type in instance search
(e.g. `HMul`), while the entry form yields a plain `Fin n`-indexed family.

Adjacent groups stack: `[i < m][j < n] f i j` elaborates the inner `[j < n] f i j` as the
row `fun j => f i j` and the outer group as `Matrix.of fun i => fun j => f i j`, which is
`Matrix.ofFun m n f` up to definitional equality.

Example (needs `open scoped Matrix`):
`θ = [i < n] ((i : ℝ) • τ)` elaborates at expected type `ℝ ^ [n, d]`.
-/
scoped syntax (name := matrixOfRows) "[" binderIdent "<" term "]" term:67 : term

open Lean Elab Term Meta in
/--
Elaborate `[i < n] body` as the matrix `Matrix.of (fun i => body)` when `body` is a row,
and as the vector `fun i => body` when it is an entry. Keeping the `Matrix.of` head for
rows preserves the `Matrix` type in instance search (e.g. `HMul`).
-/
@[term_elab matrixOfRows]
def elabMatrixOfRows : TermElab := fun stx expectedType? => do
  let (iName, n, body) ← match stx with
    | `([$i:ident < $n:term] $body) => pure (i.getId, n, body)
    | `([_ < $n:term] $body) => pure (`_, n, body)
    | _ => throwUnsupportedSyntax
  let nTy ← elabTerm (← `(Fin $n)) none
  -- When the expected type is `Fin n → _`, elaborate the body at that codomain.
  let bodyTy? ← match expectedType? with
    | none => pure none
    | some ty => do
      match ← whnf ty with
      | .forallE _ dom cod _ => if ← isDefEq dom nTy then pure (some cod) else pure none
      | _ => pure none
  -- Row iff the body is a function. Prefer the expected codomain; otherwise probe the body.
  let isRow ← match bodyTy? with
    | some ty => pure (← whnf ty).isForall
    | none => do
      let saved ← saveState
      let r ← try
          withLocalDeclD iName nTy fun _ => do
            let b ← withoutErrToSorry <| elabTerm body none
            pure (← whnf (← inferType b)).isForall
        catch ex =>
          if let .internal id _ := ex then
            if id == postponeExceptionId then throw ex
          pure true
      saved.restore
      pure r
  let lam ← match stx with
    | `([$i:ident < $n:term] $body) => `(fun ($i : Fin $n) => $body)
    | `([_ < $n:term] $body) => `(fun (_ : Fin $n) => $body)
    | _ => throwUnsupportedSyntax
  if isRow then
    elabTerm (← `(Matrix.of ($lam))) expectedType?
  else
    elabTerm lam expectedType?

end Matrix
