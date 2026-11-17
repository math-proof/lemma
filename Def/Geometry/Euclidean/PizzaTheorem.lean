/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/PizzaTheorem.lean -/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators


namespace MetaMathlibExt

section

noncomputable def pizza_q (c p : ℝ × ℝ) (φ : ℝ) : ℝ :=
  (p.1 - c.1) * Real.cos φ + (p.2 - c.2) * Real.sin φ

noncomputable def pizza_rho (c p : ℝ × ℝ) (R φ : ℝ) : ℝ :=
  -(pizza_q c p φ) + Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2)

end
end MetaMathlibExt
