/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/GreatPicard.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Order.Round
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

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
