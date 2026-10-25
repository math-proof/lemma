/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/PizzaTheorem.lean -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
open scoped BigOperators


namespace MetaMathlibExt

section

noncomputable def pizza_q (c p : ℝ × ℝ) (φ : ℝ) : ℝ :=
  (p.1 - c.1) * Real.cos φ + (p.2 - c.2) * Real.sin φ

noncomputable def pizza_rho (c p : ℝ × ℝ) (R φ : ℝ) : ℝ :=
  -(pizza_q c p φ) + Real.sqrt (R ^ 2 - ((p.1 - c.1) ^ 2 + (p.2 - c.2) ^ 2) + (pizza_q c p φ) ^ 2)

end
end MetaMathlibExt
