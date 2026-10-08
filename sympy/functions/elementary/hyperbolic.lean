import Mathlib.Analysis.Complex.Trigonometric
import sympy.core.numbers


namespace Real

/--
Hyperbolic cotangent: `coth x = 1 / tanh x`.
-/
noncomputable def coth (x : ℝ) : ℝ :=
  1 / tanh x

/--
Hyperbolic secant: `sech x = 1 / cosh x`.
-/
noncomputable def sech (x : ℝ) : ℝ :=
  1 / cosh x

/--
Hyperbolic cosecant: `csch x = 1 / sinh x`.
-/
noncomputable def csch (x : ℝ) : ℝ :=
  1 / sinh x

end Real
