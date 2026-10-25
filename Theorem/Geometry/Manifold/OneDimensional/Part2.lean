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
import Instance.Geometry.Manifold.OneDimensional
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

/-- Every `E1` atlas member is a translated `H` chart. -/
theorem omb_atlas_mem_obtain
    (e : OpenPartialHomeomorph ↥(ombInterior M) (EuclideanSpace ℝ (Fin 1)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin 1)) ↥(ombInterior M)) :
    ∃ x : ↥(ombInterior M),
      (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph = e :=
  he

/-- The transition between translated charts equals the `𝓡∂ 1` extended
coordinate change. -/
theorem omb_trans_eq_extendCoordChange (x x' : ↥(ombInterior M)) :
    Set.EqOn
      ⇑(((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans omb_interiorModelHomeomorph))
      ⇑((𝓡∂ 1).extendCoordChange (chartAt (EuclideanHalfSpace 1) x)
        (chartAt (EuclideanHalfSpace 1) x'))
      ((((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans
          omb_interiorModelHomeomorph)).source) := by
  intro y _
  rfl

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
