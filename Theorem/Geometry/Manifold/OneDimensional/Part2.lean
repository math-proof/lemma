/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/OneDimensional.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
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
public import Instance.Geometry.Manifold.OneDimensional
open scoped Manifold ContDiff Topology Bundle

public section

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
