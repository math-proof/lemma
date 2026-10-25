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
import Def.Geometry.Manifold.OneDimensional.Part3
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
/-- Radius on which the model ray stays in the chart target. -/
theorem omb_exists_halfCurve_radius (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    ∃ ε, ombGoodRadius M p ε := by
  have hmem : (𝓡∂ 1).symm (omLinEquiv 0) ∈
      (chartAt (EuclideanHalfSpace 1) p).target := by
    rw [omb_symm_ray_zero M p hp]
    exact mem_chart_target _ p
  have hcont : Continuous (fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t)) :=
    (ModelWithCorners.continuous_symm (𝓡∂ 1)).comp omLinEquiv.continuous
  have hopen : IsOpen ((fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t)) ⁻¹'
      (chartAt (EuclideanHalfSpace 1) p).target) :=
    (chartAt (EuclideanHalfSpace 1) p).open_target.preimage hcont
  obtain ⟨δ, hδpos, hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  refine ⟨min δ (1 / 2), lt_min hδpos (by norm_num), min_le_right _ _, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  have hle : |t| < δ := lt_of_lt_of_le ht (min_le_left _ _)
  simpa using hle

/-- The single coordinate of `omLinEquiv t` is `t`. -/
theorem ombLinEquiv_coord (t : ℝ) : (omLinEquiv t).ofLp 0 = t := rfl

/-- For `t ≥ 0`, the model ray lands on the coercion. -/
theorem omb_symm_ray_val_of_nonneg (t : ℝ) (ht : 0 ≤ t) :
    (((𝓡∂ 1).symm (omLinEquiv t)).val : EuclideanSpace ℝ (Fin 1)) =
      omLinEquiv t := by
  have hle : 0 ≤ (omLinEquiv t).ofLp 0 := by
    rw [ombLinEquiv_coord t]
    exact ht
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hle]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve is continuous on the symmetric interval. -/
theorem omb_halfCurve_continuousOn (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    ContinuousOn (ombHalfCurve M p) (Set.Ioo (-ε) ε) := by
  have hcont : Continuous (fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t)) :=
    (ModelWithCorners.continuous_symm (𝓡∂ 1)).comp omLinEquiv.continuous
  have hmaps : Set.MapsTo (fun t : ℝ => (𝓡∂ 1).symm (omLinEquiv t))
      (Set.Ioo (-ε) ε) (chartAt (EuclideanHalfSpace 1) p).target := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    have habs : |t| < ε := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    exact hε.2.2 t habs
  exact (chartAt (EuclideanHalfSpace 1) p).continuousOn_symm.comp
    hcont.continuousOn hmaps

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve tends to `p` from the right. -/
theorem omb_halfCurve_tendsto (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    Filter.Tendsto (ombHalfCurve M p) (nhdsWithin 0 (Set.Ioi 0)) (nhds p) := by
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε :=
    ⟨by linarith [hε.1], hε.1⟩
  have hcat : ContinuousAt (ombHalfCurve M p) 0 :=
    (omb_halfCurve_continuousOn M p ε hε).continuousAt
      (isOpen_Ioo.mem_nhds hmem0)
  have htend : Filter.Tendsto (ombHalfCurve M p) (nhds 0)
      (nhds (ombHalfCurve M p 0)) := hcat
  rw [omb_halfCurve_zero M p hp] at htend
  exact htend.mono_left nhdsWithin_le_nhds

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Vectors in `E1` are determined by their single coordinate. -/
theorem omb_E1_ext {v w : EuclideanSpace ℝ (Fin 1)}
    (h : v.ofLp 0 = w.ofLp 0) : v = w := by
  apply PiLp.ext
  intro i
  fin_cases i
  simpa using h

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Image of the half-chart curve on an initial interval. -/
theorem omb_halfCurve_image_Ico (p : M) (ε δ : ℝ)
    (hε : ombGoodRadius M p ε) (hδε : δ ≤ ε) :
    (ombHalfCurve M p) '' Set.Ico 0 δ =
      (chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | (y.val).ofLp 0 < δ} := by
  ext x
  constructor
  · rintro ⟨t, ⟨ht0, htδ⟩, rfl⟩
    have htabs : |t| < ε := by
      rw [abs_of_nonneg ht0]
      exact lt_of_lt_of_le htδ hδε
    have hT := hε.2.2 t htabs
    have hsrc : (chartAt (EuclideanHalfSpace 1) p).symm
        ((𝓡∂ 1).symm (omLinEquiv t)) ∈
        (chartAt (EuclideanHalfSpace 1) p).source :=
      (chartAt (EuclideanHalfSpace 1) p).map_target hT
    refine ⟨hsrc, ?_⟩
    have hchart : (chartAt (EuclideanHalfSpace 1) p)
        ((chartAt (EuclideanHalfSpace 1) p).symm
          ((𝓡∂ 1).symm (omLinEquiv t))) =
        (𝓡∂ 1).symm (omLinEquiv t) :=
      (chartAt (EuclideanHalfSpace 1) p).right_inv hT
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, ombHalfCurve]
    rw [hchart, omb_symm_ray_val_of_nonneg t ht0, ombLinEquiv_coord]
    exact htδ
  · rintro ⟨hxsrc, hxmem⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hxmem
    set t : ℝ := (((chartAt (EuclideanHalfSpace 1) p) x).val).ofLp 0 with ht
    have ht0 : 0 ≤ t := ((chartAt (EuclideanHalfSpace 1) p) x).property
    have htδ : t < δ := hxmem
    have htabs : |t| < ε := by
      rw [abs_of_nonneg ht0]
      exact lt_of_lt_of_le htδ hδε
    have hT := hε.2.2 t htabs
    have htIco : t ∈ Set.Ico 0 δ := ⟨ht0, htδ⟩
    refine ⟨t, htIco, ?_⟩
    simp only [ombHalfCurve]
    have hval : (((𝓡∂ 1).symm (omLinEquiv t)).val :
        EuclideanSpace ℝ (Fin 1)) =
        (((chartAt (EuclideanHalfSpace 1) p) x).val :
        EuclideanSpace ℝ (Fin 1)) := by
      rw [omb_symm_ray_val_of_nonneg t ht0]
      apply omb_E1_ext
      rw [ombLinEquiv_coord]
    have hH : (𝓡∂ 1).symm (omLinEquiv t) =
        (chartAt (EuclideanHalfSpace 1) p) x :=
      EuclideanHalfSpace.ext _ _ hval
    rw [hH]
    exact (chartAt (EuclideanHalfSpace 1) p).left_inv hxsrc

/-- Positive parameters land in the interior. -/
theorem omb_halfCurve_mem_interior (p : M) (ε t : ℝ)
    (hε : ombGoodRadius M p ε) (ht : t ∈ Set.Ioo 0 ε) :
    ombHalfCurve M p t ∈ ombInterior M := by
  rw [omb_mem_ombInterior_iff]
  rw [Set.mem_Ioo] at ht
  have htabs : |t| < ε := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have hT := hε.2.2 t htabs
  set e := chartAt (EuclideanHalfSpace 1) p with he
  have hsrc : ombHalfCurve M p t ∈ e.source := by
    simp only [ombHalfCurve]
    exact e.map_target hT
  rw [ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (n := ∞)
    (by simp : (∞ : ℕ∞ω) ≠ 0) (chart_mem_atlas _ p) hsrc]
  have hext : e.extend (𝓡∂ 1) (ombHalfCurve M p t) = omLinEquiv t := by
    simp only [ombHalfCurve, OpenPartialHomeomorph.extend_coe,
      Function.comp_apply]
    rw [e.right_inv hT]
    have hmem : omLinEquiv t ∈ Set.range (𝓡∂ 1) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ (omLinEquiv t).ofLp 0
      rw [ombLinEquiv_coord]
      exact ht.1.le
    have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
    simpa using h
  rw [hext, OpenPartialHomeomorph.extend_target]
  have hopen : IsOpen ((𝓡∂ 1).symm ⁻¹' e.target) :=
    e.open_target.preimage (ModelWithCorners.continuous_symm (𝓡∂ 1))
  rw [interior_inter, hopen.interior_eq,
    interior_range_modelWithCornersEuclideanHalfSpace 1]
  refine ⟨?_, ?_⟩
  · exact hT
  · change 0 < (omLinEquiv t).ofLp 0
    rw [ombLinEquiv_coord]
    exact ht.1

/-- A boundary point is not in the interior. -/
theorem omb_boundary_not_mem_interior (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) : p ∉ ombInterior M := by
  rw [omb_mem_ombInterior_iff]
  have h := (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint p).mp hp
  exact h

/-- Model identity: the ray meets the left Icc chart. -/
theorem omb_symm_leftChart (z : Set.Icc (0 : ℝ) 1) :
    (𝓡∂ 1).symm (omLinEquiv z.val) = IccLeftChart 0 1 z := by
  have hnonneg : 0 ≤ (z.val : ℝ) := z.property.1
  apply EuclideanHalfSpace.ext
  rw [omb_symm_ray_val_of_nonneg _ hnonneg]
  apply omb_E1_ext
  rw [ombLinEquiv_coord, IccLeftChart_apply]
  simp

/-- Model identity: the ray meets the right Icc chart. -/
theorem omb_symm_rightChart (z : Set.Icc (0 : ℝ) 1) :
    (𝓡∂ 1).symm (omLinEquiv (1 - z.val)) = IccRightChart 0 1 z := by
  have hnonneg : 0 ≤ (1 - z.val : ℝ) := by
    have hle : z.val ≤ 1 := z.property.2
    linarith
  apply EuclideanHalfSpace.ext
  rw [omb_symm_ray_val_of_nonneg _ hnonneg]
  apply omb_E1_ext
  rw [ombLinEquiv_coord, IccRightChart_apply]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve meets the left Icc chart. -/
theorem omb_halfCurve_leftChart (p : M) (z : Set.Icc (0 : ℝ) 1) :
    ombHalfCurve M p z.val =
      (chartAt (EuclideanHalfSpace 1) p).symm (IccLeftChart 0 1 z) := by
  simp only [ombHalfCurve, omb_symm_leftChart]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The reflected half-chart curve meets the right Icc chart. -/
theorem omb_halfCurve_rightChart (p : M) (z : Set.Icc (0 : ℝ) 1) :
    ombHalfCurve M p (1 - z.val) =
      (chartAt (EuclideanHalfSpace 1) p).symm (IccRightChart 0 1 z) := by
  simp only [ombHalfCurve, omb_symm_rightChart]

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
