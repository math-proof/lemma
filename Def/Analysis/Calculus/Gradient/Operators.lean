module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Syntax.Analysis.Calculus.Gradient.Operators


@[expose] public section

/-- Strip outer term parentheses so `∇[θ] (F θ)` and `∇[θ] F θ` share one match. -/
partial def GradSugar.stripParen : Lean.TSyntax `term → Lean.MacroM (Lean.TSyntax `term)
  | `(($e)) => stripParen e
  | e => pure e

@[expose] public meta section

/-- Infoview: `gradient (fun θ ↦ e) θ` ↦ `∇[θ] e`; `gradient (fun θ ↦ e) p` ↦ `∇[θ = p] e`;
non-lambda `gradient F p` with `p` an ident ↦ `∇[p] (F p)`. -/
@[app_unexpander gradient]
meta def gradient.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $p) =>
    match f with
    | `(fun $x:ident ↦ $body) => do
      if let `($y:ident) := p then
        if x.getId == y.getId then return ← `(∇[$x] $body)
      `(∇[$x = $p] $body)
    | _ => do
      if let `($y:ident) := p then
        return ← `(∇[$y] ($f $y))
      throw ()
  | _ => throw ()

