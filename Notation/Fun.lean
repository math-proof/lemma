module

public import Structure.Data.List.Slice

@[expose] public section

open Lean

/-- Open-ended `x[t:]` (elaborator-owned). Avoids importing cyclic
`Syntax.Data.List` ↔ `Def.Data.List.List`. `Syntax.Data.List` should drop its duplicate of
this one form; closed-slice syntax stays there. -/
syntax:max term noWs "[" withoutPosition(term:60) ":]" : term

open Elab Term Meta in
/-- `r[t:]` on a bare `ℕ → α` or a list is elaborated by `Syntax.Data.List`; this elaborator
only declines, so that elaborator runs. -/
@[term_elab «term__[_:]»]
meta def Fun.elabGetSliceFrom : TermElab := fun _ _ => throwUnsupportedSyntax

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
meta def Function.getSlice.unexpand : PrettyPrinter.Unexpander
  | _ => throw ()

/-- NumPy-style top-left block: `y[:i, :j]` for `y : ℕ → ℕ → α`. -/
def Function.getSlice2 {α : Type*} (y : ℕ → ℕ → α) (rows cols : ℕ) :
    Fin rows → Fin cols → α :=
  fun i j => y i j

/-- NumPy `x[:i, :j]` / `x[:i,:j]` (elaborator-owned; `[:n]` alone stays in `Syntax.Data.List`).
Closest nested form `x[0:i, 0:j]` still expands via `Syntax.Data.List` to `(x[0:i])[0:j]`,
which is not the 2D top-left block — prefer `x[:i, :j]` or `getSlice2`. -/
syntax:max term noWs "[:" withoutPosition(term:60) "," ":" withoutPosition(term:60) "]" : term

open Elab Term Meta in
/-- `y[:i, :j]` → `Function.getSlice2`. -/
@[term_elab «term__[:_,:_]»]
meta def Fun.elabGetSlice2 : TermElab := fun stx expectedType? =>
  match stx with
  | `($x[:$rows, :$cols]) => do elabTerm (← `(Function.getSlice2 $x $rows $cols)) expectedType?
  | _ => throwUnsupportedSyntax

/-- Flip `y[:i, :j] : Fin i → Fin j → Ω → α` to an `Ω`-first random matrix
(so it can sit next to `y[i][:j] : Ω → Fin j → α` as an IndepFun operand). -/
instance {r c : ℕ} {Ω α : Type*} :
    Coe (Fin r → Fin c → Ω → α) (Ω → Fin r → Fin c → α) where
  coe f := fun ω i j => f i j ω

instance {r c : ℕ} {Ω α : Type*} :
    CoeFun (Fin r → Fin c → Ω → α) (fun _ => Ω → Fin r → Fin c → α) where
  coe f := fun ω i j => f i j ω
