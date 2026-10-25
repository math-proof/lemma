import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.Complex.FatouRadial
open MeasureTheory Complex Set Filter Metric
open scoped Topology


namespace Complex.FatouRadialWanted

noncomputable def fatouKernel (r t : ℝ) : ℝ :=
  (1 - r ^ 2) * Real.sin t / (1 - 2 * r * Real.cos t + r ^ 2) ^ 2

end Complex.FatouRadialWanted
