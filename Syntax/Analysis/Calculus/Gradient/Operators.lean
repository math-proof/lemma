import Mathlib.Analysis.Calculus.Gradient.Basic
import Notation.Analysis.Calculus.Gradient.Operators


syntax:max (name := gradSugar) "∇[" ident "] " term:67 : term

/-- `∇[θ = θ₀] expr`: the gradient of `expr` with respect to `θ`, evaluated at `θ₀`. -/
syntax:max (name := gradAtSugar) "∇[" ident " = " term "] " term:67 : term

