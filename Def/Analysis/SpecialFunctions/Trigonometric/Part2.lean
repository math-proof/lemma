module

public import Mathlib.Tactic
public import Mathlib.Analysis.Complex.Trigonometric
public import Instance.Analysis.Real.Numbers
public import Instance.Analysis.SpecialFunctions.Trigonometric

@[expose] public section

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
