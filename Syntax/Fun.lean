import Lean.Elab.Term
import Structure.Fun

open Lean Elab Term Meta in
/-- `f[i]` when `f : Fun ι α`: elaborate the index at type `ι`.
`GetElem`'s `idx` is not an outParam, so under binders like `sup[t] |δ[t]| < ∞`
(where `t` starts as a metavariable) the default `getElem` / `get_elem_tactic`
path fails with "failed to prove index is valid". Non-`Fun` collections
`throwUnsupportedSyntax` so Array/List GetElem stay unchanged. -/
elab_rules : term
  | `(getElem $x $i $_) => do
    let saved ← saveState
    let funData? ← try
        let xE ← withoutErrToSorry <| elabTerm x none
        let ty ← whnfR (← instantiateMVars (← inferType xE))
        match ty with
        | .app (.app (.const n _) ι) _ =>
            if n == ``Fun then pure (some (xE, ι)) else pure none
        | _ => pure none
      catch _ =>
        pure none
    let some (xE, ι) := funData? | do
      saved.restore
      throwUnsupportedSyntax
    let iE ← elabTermEnsuringType i ι
    -- defeq to `getElem x i trivial` via `Fun.getElem_eq`
    mkAppM ``Fun.toFun #[xE, iE]
