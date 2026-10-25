import Structure.Fun
import stdlib.List

namespace Fun

/-- Open-ended path slice: `r[t:]` for `r : Fun ℕ α` is `k ↦ r.toFun (t + k)`,
same shape as `Function.getSliceFrom` on bare sequences (so `@` / Dot keep working). -/
def getSliceFrom (f : Fun ℕ α) (t : ℕ) : ℕ → α :=
  fun k ↦ f.toFun (t + k)

end Fun

open Lean Elab Term Meta in
/-- `r[t:]` when `r : Fun ℕ _` → `Fun.getSliceFrom r t`.
Otherwise `throwUnsupportedSyntax` so `stdlib.List`'s elaborator handles bare `ℕ → α` / lists. -/
@[term_elab «term__[_:]»]
def Fun.elabGetSliceFrom : TermElab := fun stx expectedType? =>
  match stx with
  | `($x[$start :]) => do
    let saved ← saveState
    let ty? ← try
        let e ← withoutErrToSorry <| elabTerm x none
        pure (some (← whnfR (← instantiateMVars (← inferType e))))
      catch _ => pure none
    saved.restore
    let isFun := match ty? with
      | some (.app (.app (.const n _) d) _) =>
          n == ``Fun && d.isConstOf ``Nat
      | _ => false
    unless isFun do throwUnsupportedSyntax
    elabTerm (← `(Fun.getSliceFrom $x ($start))) expectedType?
  | _ => throwUnsupportedSyntax

namespace Fun

/-- Infoview: print `Fun.getSliceFrom r t` as `r[t:]`. -/
@[app_unexpander getSliceFrom]
def getSliceFrom.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $t) => `($f[$t :])
  | `($_ $f $t $k) => `($f[$t :] $k)
  | _ => throw ()

end Fun
