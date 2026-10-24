/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/GreatPicard.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Lemma.Complex.Bloch
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Topology.Algebra.Order.Field

open Set Filter Topology Metric

namespace MathlibExt.Analysis.Complex.GreatPicardWanted

/-!
# Great Picard theorem (essential singularity)
-/

/-- `f` has an essential isolated singularity at `c`: holomorphic on some punctured ball
around `c` with no finite limit and no pole at `c`. -/
def IsEssentialIsolatedSingularityAt (f : ℂ → ℂ) (c : ℂ) : Prop :=
  (∃ r : ℝ, 0 < r ∧ DifferentiableOn ℂ f (Metric.ball c r \ {c})) ∧
  ¬ (∃ l : ℂ, Tendsto f (𝓝[≠] c) (𝓝 l)) ∧
  ¬ Tendsto (fun z => ‖f z‖) (𝓝[≠] c) Filter.atTop
end MathlibExt.Analysis.Complex.GreatPicardWanted
