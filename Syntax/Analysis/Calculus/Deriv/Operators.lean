import Mathlib.Analysis.Calculus.Deriv.Basic
import Notation.Analysis.Calculus.Deriv.Operators
import Def.Analysis.Calculus.Gradient.Operators
import Lean.Elab.Term


/-- One or more binders: `∂[t] body`, or `∂[x, y] body` = `∂[y] (∂[x] body)`. -/
syntax:max (name := derivSugar) "∂[" ident,+ "] " term:67 : term

/-- `∂[t = t₀] expr`: derivative in `t`, evaluated at `t₀`.

When `t₀ : ℝ` this is ordinary evaluation of `(fun t ↦ ∂[t] expr)`. When `t₀ : ℝ*`
and `Instance.Analysis.Hyperreal.Coe` is in scope, that `ℝ → ℝ` map is coerced to
`ℝ* → ℝ*` (`Germ.map`) so Hyperreal ends such as `∂[x = x + Δx] u t x` elaborate.
The result is wrapped as `@id (typeof t₀) …` so the surface type stays `ℝ*` (not the
unfolded `Germ`/`Quot`), and field notation like `.arctan` resolves to `Hyperreal.arctan`. -/
syntax:max (name := derivAtSugar) "∂[" ident " = " term "] " term:67 : term

macro_rules
  | `(∂[$xs:ident,*] $body) => do
    let ids := xs.getElems
    if ids.size == 1 then
      let x := ids[0]!
      let b ← GradSugar.stripParen body
      match b with
      | `($f $y:ident) =>
        if y.getId == x.getId then
          `(deriv $f $x)
        else
          `(deriv (fun $x:ident ↦ $body) $x)
      | `($j:ident) =>
        `(deriv $j $x)
      | _ =>
        `(deriv (fun $x:ident ↦ $body) $x)
    else
      -- `∂[x, y, …] body` = `∂[y] (∂[x] body)` … (left binders innermost)
      let x0 := ids[0]!
      let mut acc ← `(∂[$x0] $body)
      for x in ids[1:] do
        acc ← `(∂[$x] $acc)
      pure acc

open Lean Elab Term Meta in
/-- Point form: elaborate `p` first, build `(fun x ↦ ∂[x] body) : ℝ → ℝ`, coerce that
map to `typeof(p) → typeof(p)` (ℝ stays ℝ; ℝ* uses `Coe`/`Germ.map` when in scope),
apply, then wrap with `@id typeof(p)` so Hyperreal ends keep surface type `ℝ*` for
field notation (bare `Germ.map …` elaborates as `Germ`/`Quot`, so `.arctan` fails). -/
elab_rules : term
  | `(derivAtSugar| ∂[$x:ident = $p] $body) => do
    let pE ← elabTerm p none
    synthesizeSyntheticMVarsNoPostponing
    let pE ← instantiateMVars pE
    let pTy ← inferType pE
    let real := Lean.mkConst ``Real
    let fE ← elabTerm (← `(fun $x:ident ↦ (∂[$x] $body))) (some (← mkArrow real real))
    synthesizeSyntheticMVarsNoPostponing
    let fE ← instantiateMVars fE
    let expectedFnTy ← mkArrow pTy pTy
    let fCoe ← Term.ensureHasType (some expectedFnTy) fE
    let app := mkApp fCoe pE
    -- `@id pTy app` keeps Hyperreal (not unfolded Germ/Quot) for `.arctan` etc.
    mkAppOptM ``id #[some pTy, some app]
