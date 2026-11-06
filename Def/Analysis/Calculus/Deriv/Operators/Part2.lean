import Mathlib.Analysis.Calculus.Deriv.Basic
import Syntax.Analysis.Calculus.Deriv.Operators


/-- Infoview: `deriv (fun t ↦ e) t` ↦ `∂[t] e`; `deriv (fun t ↦ e) p` ↦ `∂[t = p] e`;
non-lambda `deriv F p` with `p` an ident ↦ `∂[p] (F p)`. -/
@[app_unexpander deriv]
def deriv.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $p) =>
    match f with
    | `(fun $x:ident ↦ $body) => do
      if let `($y:ident) := p then
        if x.getId == y.getId then return ← `(∂[$x] $body)
      `(∂[$x = $p] $body)
    | _ => do
      if let `($y:ident) := p then
        return ← `(∂[$y] ($f $y))
      throw ()
  | _ => throw ()
