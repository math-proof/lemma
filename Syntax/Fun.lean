import Lean.Elab.Term
import Structure.Fun

open Lean Elab Term Meta in
/-- `f[i]` when `f : Fun ι α` or `f : PiFun α`: elaborate the index at type `ι`.
`GetElem`'s `idx` is not an outParam, and `PiFun` has a dependent element type, so the
default `getElem` path cannot type `Z[k]`. Non-`Fun` collections
`throwUnsupportedSyntax` so Array/List GetElem stay unchanged. -/
elab_rules : term
  | `(getElem $x $i $_) => do
    let saved ← saveState
    let funData? ← try
        let xE ← withoutErrToSorry <| elabTerm x none
        let ty ← whnfR (← instantiateMVars (← inferType xE))
        match ty with
        | .app (.app (.const n _) ι) _ =>
            if n == ``Fun then pure (some (xE, ι, ``Fun.toFun))
            else if n == ``PiFun then pure (some (xE, ι, ``PiFun.toFun))
            else pure none
        | _ => pure none
      catch _ =>
        pure none
    let some (xE, ι, toFun) := funData? | do
      saved.restore
      throwUnsupportedSyntax
    let iE ← elabTermEnsuringType i ι
    mkAppM toFun #[xE, iE]
