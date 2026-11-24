module
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Theorem.Set.Manifold.RiemannianMetricExistence
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Theorem.Geometry.Manifold.OneDimensional.Part3
open scoped Manifold ContDiff Topology Bundle


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
section LocalDiffeomorphConstructors

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

end LocalDiffeomorphConstructors
section IntervalParametrisation
end IntervalParametrisation
section InverseFunction1D
end InverseFunction1D
noncomputable section

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

section BoundaryInterior

/-- Good radius bundle for the half-chart curve at `p`. -/
def ombGoodRadius (p : M) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧
    ∀ t : ℝ, |t| < ε → (𝓡∂ 1).symm (omLinEquiv t) ∈
      (chartAt (EuclideanHalfSpace 1) p).target

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
