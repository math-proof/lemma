import Structure.Fun
import Structure.Data.List.Slice
open Lean

/-- Type sugar: `ℕ ⇀ ℝ` means `Fun ℕ ℝ` (same precedence as `→`).
Semantic indexed-→ / function arrow (⇀, LaTeX \rightharpoonup). -/
infixr:25 " ⇀ " => Fun

namespace Fun

instance : CoeFun (Fun ι α) (fun _ => ι → α) where
  coe := toFun

instance : GetElem (Fun ι α) ι α (fun _ _ => True) where
  getElem f i _ := f.toFun i

/-- Open-ended path slice: `r[t:]` for `r : Fun ℕ α` is `k ↦ r.toFun (t + k)`,
same shape as `Function.getSliceFrom` on bare sequences (so `@` / Dot keep working). -/
def getSliceFrom (f : Fun ℕ α) (t : ℕ) : ℕ → α :=
  fun k ↦ f.toFun (t + k)

end Fun

/-- Open-ended `x[t:]` (elaborator-owned). Avoids importing cyclic
`Syntax.Data.List` ↔ `Def.Data.List.List`. `Syntax.Data.List` should drop its duplicate of
this one form; closed-slice syntax stays there. -/
syntax:max term noWs "[" withoutPosition(term:60) ":]" : term

open Elab Term Meta in
/-- `r[t:]` when `r : Fun ℕ _` → `Fun.getSliceFrom r t`.
Otherwise `throwUnsupportedSyntax` so other elaborators handle bare `ℕ → α` / lists. -/
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
def getSliceFrom.unexpand : PrettyPrinter.Unexpander
  | `($_ $f $t) => `($f[$t :])
  | `($_ $f $t $k) => `($f[$t :] $k)
  | _ => throw ()

end Fun

/-- Slicing of a function `ℕ → β`, dispatched on its value type `β`. The random-variable
instance stays in `Def.Probability.Process.HiddenMarkovSequence.Part2`. -/
class FunSlice (β : Type*) where
  Out : Slice → Type*
  slice : (ℕ → β) → (s : Slice) → Out s

/-- `f[a:b]` for `f : ℕ → α`: the vector `(f a, …, f (b-1)) : Fin (b - a) → α`. -/
instance (priority := low) {α : Type*} : FunSlice α where
  Out s := Fin (s.stop.toNat - s.start.toNat) → α
  slice f s := fun i => f (i.val + s.start.toNat)

/-- Python slicing of a function on `ℕ` (`f[:n]`, `f[a:b]`). Only unit step is supported. -/
def Function.getSlice {β : Type*} [FunSlice β] (x : ℕ → β) (s : Slice) : FunSlice.Out β s :=
  FunSlice.slice x s

/-- Closed-slice infoview sugar needs `Syntax.Data.List` slice forms; skip here to stay
cycle-free. Prefer importing that module at use sites that care about `f[a:b]` pretty-printing. -/
@[app_unexpander Function.getSlice]
def Function.getSlice.unexpand : PrettyPrinter.Unexpander
  | _ => throw ()

namespace Fun

/-- Closed slices on `Fun ℕ α` (`f[:n]`, `f[a:b]`). Reducible so coercions see the bare slice. -/
abbrev getSlice {α : Type*} [FunSlice α] (f : Fun ℕ α) (s : Slice) : FunSlice.Out α s :=
  Function.getSlice f.toFun s

@[app_unexpander Fun.getSlice]
def getSlice.unexpand : PrettyPrinter.Unexpander
  | _ => throw ()

end Fun
