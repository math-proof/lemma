import Def.Data.List.Slice
import Syntax.Data.List.List
open Lean


/-- Python's open-ended slice `f[t:]` of an infinite sequence `f : ℕ → α`: the shifted sequence
`k ↦ f (t + k)`, again of type `ℕ → α` (so e.g. `(fun k ↦ γ ^ k) @ r[t:] = ∑' k, γ ^ k * r (t + k)`). -/
def Function.getSliceFrom (f : ℕ → α) (t : ℕ) : ℕ → α := fun k ↦ f (t + k)

open Elab Term Meta in
/-- `x[start:]`: for a sequence `x : ℕ → α` it is `Function.getSliceFrom x start : ℕ → α`; for any
other receiver (lists, vectors, tensors, …) it is `x.getSlice ⟨start, x.length, 1⟩` as before.
The receiver's type is inspected (without committing the elaboration) to choose the expansion. -/
@[term_elab «term__[_:]»]
def Slice.elabGetSliceFrom : TermElab := fun stx expectedType? =>
  match stx with
  | `($x[$start :]) => do
    let saved ← saveState
    let ty? ← try
        let e ← withoutErrToSorry <| elabTerm x none
        pure (some (← whnfR (← instantiateMVars (← inferType e))))
      catch _ => pure none
    saved.restore
    if let some ty := ty? then
      if ty.isMVar then tryPostpone
    let isSeq := match ty? with
      | some (.forallE _ d b _) => d.isConstOf ``Nat && !b.hasLooseBVars
      | _ => false
    if isSeq then
      elabTerm (← `(Function.getSliceFrom $x ($start))) expectedType?
    else
      elabTerm (← `(($x).getSlice ⟨($start : ℤ), (($x).length : ℤ), (1 : ℤ)⟩)) expectedType?
  | _ => throwUnsupportedSyntax

/-- Infoview: print `Function.getSliceFrom f t` as `f[t:]`. -/
@[app_unexpander Function.getSliceFrom]
def Function.getSliceFrom.unexpand : PrettyPrinter.Unexpander
  | `($_ $f $t) => `($f[$t :])
  | `($_ $f $t $k) => `($f[$t :] $k)
  | _ => throw ()

