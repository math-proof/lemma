/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Geometry.Manifold.Instances.Sphere
import Lemma.Set.Manifold.RiemannianMetricExistence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Def.Geometry.Manifold.OneDimensional.Part2
open scoped Manifold ContDiff Topology Bundle


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

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- At a boundary point, the chart sends `p` to the corner `0`. -/
theorem omb_chartAt_boundary_val (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    ((((chartAt (EuclideanHalfSpace 1) p) p).val :
      EuclideanSpace ℝ (Fin 1))) = 0 := by
  have h := ModelWithCorners.isBoundaryPoint_iff.mp hp
  rw [frontier_range_modelWithCornersEuclideanHalfSpace 1] at h
  have h' : 0 = (extChartAt (𝓡∂ 1) p p).ofLp 0 := h
  have heq : extChartAt (𝓡∂ 1) p p =
      ((((chartAt (EuclideanHalfSpace 1) p) p).val :
        EuclideanSpace ℝ (Fin 1))) := rfl
  rw [heq] at h'
  have hcoord : ((((chartAt (EuclideanHalfSpace 1) p) p).val :
      EuclideanSpace ℝ (Fin 1))).ofLp 0 = 0 := h'.symm
  apply PiLp.ext
  intro i
  fin_cases i
  simpa using hcoord

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The model ray at `0` hits the chart value of `p`. -/
theorem omb_symm_ray_zero (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    (𝓡∂ 1).symm (omLinEquiv 0) = (chartAt (EuclideanHalfSpace 1) p) p := by
  have hvec := omb_chartAt_boundary_val M p hp
  rw [map_zero]
  have hsym0 : (𝓡∂ 1).symm (0 : EuclideanSpace ℝ (Fin 1)) =
      (⟨0, le_refl _⟩ : EuclideanHalfSpace 1) :=
    modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_refl _)
  rw [hsym0]
  apply Subtype.ext
  rw [hvec]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve starts at `p`. -/
theorem omb_halfCurve_zero (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) : ombHalfCurve M p 0 = p := by
  simp only [ombHalfCurve]
  rw [omb_symm_ray_zero M p hp]
  exact (chartAt (EuclideanHalfSpace 1) p).left_inv (mem_chart_source _ p)

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
