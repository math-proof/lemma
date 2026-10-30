import Mathlib.Analysis.Calculus.Gradient.Basic
import Syntax.Analysis.Calculus.Gradient.Operators


/-- Infoview: `gradient (fun θ ↦ e) θ` ↦ `∇[θ] e`; `gradient (fun θ ↦ e) p` ↦ `∇[θ = p] e`;
non-lambda `gradient F p` with `p` an ident ↦ `∇[p] (F p)`. -/
@[app_unexpander gradient]
def gradient.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $p) =>
    match f with
    | `(fun $x:ident ↦ $body) => do
      if let `($y:ident) := p then
        if x.getId == y.getId then return ← `(∇[$x] $body)
      `(∇[$x = $p] $body)
    | _ => do
      if let `($y:ident) := p then
        return ← `(∇[$y] ($f $y))
      `(∇ $f $p)
  | _ => throw ()

