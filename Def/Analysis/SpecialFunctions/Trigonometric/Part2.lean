import Mathlib.Tactic
import Mathlib.Analysis.Complex.Trigonometric
import Instance.Analysis.Real.Numbers
import Instance.Analysis.SpecialFunctions.Trigonometric
export Real (cos sin arccos arcsin tan cot)


namespace Real

/--
Cosecant: `csc x = 1 / sin x`.
-/
noncomputable def csc (x : ℝ) : ℝ :=
  1 / sin x

/--
Secant: `sec x = 1 / cos x`.
-/
noncomputable def sec (x : ℝ) : ℝ :=
  1 / cos x

end Real
