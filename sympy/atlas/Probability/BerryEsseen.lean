/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BerryEsseen.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Separation.CompletelyRegular

section
open MeasureTheory ProbabilityTheory Finset Set
open scoped ProbabilityTheory ENNReal NNReal

namespace MathlibExt.Probability.BerryEsseenWanted

/-!
# Berry–Esseen theorem

The uniform CLT rate for normalized i.i.d. sums.
-/

private noncomputable def stdNormalCDF (w : ℝ) : ℝ := (gaussianReal 0 1).real (Set.Iic w)

private noncomputable def steinEg (w : ℝ) : ℝ := Real.sqrt (2 * Real.pi) * Real.exp (w ^ 2 / 2)

private noncomputable def steinSolution (z w : ℝ) : ℝ :=
  (stdNormalCDF (min w z) - stdNormalCDF w * stdNormalCDF z) * steinEg w

private noncomputable def steinSolutionDeriv (z w : ℝ) : ℝ :=
  w * steinSolution z w + (if w ≤ z then (1 : ℝ) else 0) - stdNormalCDF z

/-- Indicator window: 1 if `|y - z| ≤ |x|`, else 0. -/
private noncomputable def steinWindow (y x z : ℝ) : ℝ :=
  if |y - z| ≤ |x| then 1 else 0

/-- Clamp function for the concentration inequality. -/
private noncomputable def clampFun (a b δ : ℝ) (w : ℝ) : ℝ :=
  max (a - δ) (min w (b + δ)) - (a + b) / 2

/-- The summand `h(x) = min δ |x| · |x|` for the concentration proof. -/
private noncomputable def concH (δ : ℝ) (x : ℝ) : ℝ :=
  min δ |x| * |x|
end MathlibExt.Probability.BerryEsseenWanted
end
