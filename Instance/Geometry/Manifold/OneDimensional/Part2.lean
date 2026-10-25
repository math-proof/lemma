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
import Theorem.Geometry.Manifold.OneDimensional.Part2
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

/-- The interior is a boundaryless `E1` manifold. -/
instance ombIsManifoldInterior :
    IsManifold (𝓡 1) ∞ ↥(ombInterior M) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨x, rfl⟩ := omb_atlas_mem_obtain M e he
  obtain ⟨x', rfl⟩ := omb_atlas_mem_obtain M e' he'
  have hAmax : (chartAt (EuclideanHalfSpace 1) x) ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ ↥(ombInterior M) :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas _ x)
  have hA'max : (chartAt (EuclideanHalfSpace 1) x') ∈
      IsManifold.maximalAtlas (𝓡∂ 1) ∞ ↥(ombInterior M) :=
    IsManifold.subset_maximalAtlas (chart_mem_atlas _ x')
  have hE := ModelWithCorners.contDiffOn_extendCoordChange hAmax hA'max
  have hfun := omb_trans_eq_extendCoordChange M x x'
  have hsub : ((((chartAt (EuclideanHalfSpace 1) x).trans
      omb_interiorModelHomeomorph).symm ≫ₕ
      ((chartAt (EuclideanHalfSpace 1) x').trans
        omb_interiorModelHomeomorph)).source) ⊆
      (((𝓡∂ 1).extendCoordChange (chartAt (EuclideanHalfSpace 1) x)
        (chartAt (EuclideanHalfSpace 1) x')).source) := by
    intro y hy
    rw [ModelWithCorners.extendCoordChange_source]
    rw [OpenPartialHomeomorph.trans_source] at hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [OpenPartialHomeomorph.symm_source] at hy1
    have himg : y ∈ ((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph) ''
        (((chartAt (EuclideanHalfSpace 1) x).trans
          omb_interiorModelHomeomorph).source) := by
      rw [OpenPartialHomeomorph.image_source_eq_target]
      exact hy1
    obtain ⟨z, hz, hzy⟩ := himg
    rw [OpenPartialHomeomorph.trans_source] at hz
    obtain ⟨hzA, hzι⟩ := hz
    have hzy' : omb_interiorModelHomeomorph
        ((chartAt (EuclideanHalfSpace 1) x) z) = y := hzy
    have hyι : y ∈ omb_interiorModelHomeomorph.target := by
      rw [← hzy']
      exact omb_interiorModelHomeomorph.map_source hzι
    have hyinv : omb_interiorModelHomeomorph.symm y =
        (chartAt (EuclideanHalfSpace 1) x) z := by
      rw [← hzy']
      exact omb_interiorModelHomeomorph.left_inv hzι
    have hsymsrc : omb_interiorModelHomeomorph.symm y ∈
        ((chartAt (EuclideanHalfSpace 1) x).symm ≫ₕ
          (chartAt (EuclideanHalfSpace 1) x')).source := by
      rw [OpenPartialHomeomorph.trans_source]
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.symm_source, hyinv]
        exact (chartAt (EuclideanHalfSpace 1) x).map_source hzA
      · have hmem2 : ((chartAt (EuclideanHalfSpace 1) x).trans
            omb_interiorModelHomeomorph).symm y ∈
            ((chartAt (EuclideanHalfSpace 1) x').trans
              omb_interiorModelHomeomorph).source := hy2
        rw [OpenPartialHomeomorph.trans_source] at hmem2
        obtain ⟨hmem2A, -⟩ := hmem2
        have e2 : ((chartAt (EuclideanHalfSpace 1) x).trans
            omb_interiorModelHomeomorph).symm y = z := by
          change (chartAt (EuclideanHalfSpace 1) x).symm
            (omb_interiorModelHomeomorph.symm y) = z
          rw [hyinv]
          exact (chartAt (EuclideanHalfSpace 1) x).left_inv hzA
        rw [e2] at hmem2A
        have e3 : (chartAt (EuclideanHalfSpace 1) x).symm
            (omb_interiorModelHomeomorph.symm y) = z := by
          rw [hyinv]
          exact (chartAt (EuclideanHalfSpace 1) x).left_inv hzA
        rw [Set.mem_preimage, e3]
        exact hmem2A
    refine ⟨omb_interiorModelHomeomorph.symm y, hsymsrc, ?_⟩
    calc (𝓡∂ 1) (omb_interiorModelHomeomorph.symm y)
        = omb_interiorModelHomeomorph (omb_interiorModelHomeomorph.symm y) :=
          rfl
      _ = y := omb_interiorModelHomeomorph.right_inv hyι
  have hT : ContDiffOn ℝ ∞
      ⇑(((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans omb_interiorModelHomeomorph))
      ((((chartAt (EuclideanHalfSpace 1) x).trans
        omb_interiorModelHomeomorph).symm ≫ₕ
        ((chartAt (EuclideanHalfSpace 1) x').trans
          omb_interiorModelHomeomorph)).source) :=
    (hE.mono hsub).congr hfun
  refine ContDiffOn.congr_mono hT (fun z _ => ?_) (fun z hz => hz.1)
  rfl

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
