import Mathlib.Analysis.Calculus.Gradient.Basic
import Notation.Analysis.Calculus.Gradient.Operators


syntax:max (name := gradSugar) "∇[" ident "] " term:67 : term

/-- `∇[θ = θ₀] expr`: the gradient of `expr` with respect to `θ`, evaluated at `θ₀`. -/
syntax:max (name := gradAtSugar) "∇[" ident " = " term "] " term:67 : term

macro_rules
  | `(∇[$x:ident] $body) => do
    let b ← GradSugar.stripParen body
    match b with
    | `($f $y:ident) =>
      if y.getId == x.getId then
        `(gradient $f $x)
      else
        `(gradient (fun $x:ident ↦ $body) $x)
    | `($j:ident) =>
      `(gradient $j $x)
    | _ =>
      `(gradient (fun $x:ident ↦ $body) $x)
  | `(∇[$x:ident = $p] $body) => do
    let b ← GradSugar.stripParen body
    match b with
    | `($f $y:ident) =>
      if y.getId == x.getId then
        `(gradient $f $p)
      else
        `(gradient (fun $x:ident ↦ $body) $p)
    | `($j:ident) =>
      `(gradient $j $p)
    | _ =>
      `(gradient (fun $x:ident ↦ $body) $p)
