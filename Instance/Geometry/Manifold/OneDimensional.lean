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
import Theorem.Geometry.Manifold.OneDimensional
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

/-- The interior carries `E1` charts: the `H` chart followed by `ι`. -/
instance ombChartedSpaceInterior :
    ChartedSpace (EuclideanSpace ℝ (Fin 1)) ↥(ombInterior M) where
  atlas := Set.range fun x : ↥(ombInterior M) =>
    (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph
  chartAt x := (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph
  mem_chart_source := by
    intro x
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨mem_chart_source _ x, ?_⟩
    have hx : (𝓡∂ 1).IsInteriorPoint (x.val) := x.2
    have hnhds := range_mem_nhds_isInteriorPoint hx
    have hmem : (𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) x) x) ∈
        interior (Set.range (𝓡∂ 1)) := by
      rw [mem_interior_iff_mem_nhds]
      exact hnhds
    rw [interior_range_modelWithCornersEuclideanHalfSpace 1] at hmem
    have hpos : 0 < (((chartAt (EuclideanHalfSpace 1) x) x).val).ofLp 0 := hmem
    exact hpos
  chart_mem_atlas := fun x => Set.mem_range_self x

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
