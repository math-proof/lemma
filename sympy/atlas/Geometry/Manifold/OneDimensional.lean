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

open scoped Manifold ContDiff Topology Bundle

noncomputable section

namespace MathlibExt.Geometry.Manifold.OneDimensionalClassification

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
section SpeedSetup
/-- Squared speed of a curve `γ : ℝ → M` at `t`, measured with the metric `g`.
If `γ` is not differentiable at `t`, `mfderiv` is `0`, so the speed is `0`. -/
private def omCurveSpeedSq
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) γ t (1 : ℝ))

/-- The constant-velocity section `s ↦ (s, 1)` into `ModelProd ℝ ℝ`, with the
`ModelProd` codomain so that smoothness statements resolve the `chartedSpaceSelf`
instance (matching `tangentBundleModelSpaceHomeomorph`). -/
private def omPairFn : ℝ → ModelProd ℝ ℝ := fun s => (s, (1 : ℝ))

/-- `γ` has unit speed on `U`: it is smooth and its squared speed is `1`. -/
private def omIsUnitSpeedOn
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (γ : ℝ → M) (U : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ γ U ∧ ∀ t ∈ U, omCurveSpeedSq g γ t = 1

end SpeedSetup
section ArcLengthIntegral
end ArcLengthIntegral
section UnitSpeedCharts
/-- The linear identification `ℝ ≃L[ℝ] E1`. -/
private def omLinEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (Fin 1) ℝ).symm
end UnitSpeedCharts
section IdentityTheorem
end IdentityTheorem
section MaximalCurve

/-- An admissible pair: an open connected neighbourhood of `0` carrying a
unit-speed curve that agrees with the base chart near `0`. -/
private def omAdmissible
    (g : Bundle.ContMDiffRiemannianMetric (𝓡 1) ∞ (EuclideanSpace ℝ (Fin 1))
      (fun x : M => TangentSpace (𝓡 1) x))
    (α0 : PartialDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ℝ M ∞) (J : Set ℝ) (δ : ℝ → M) : Prop :=
  IsOpen J ∧ J.OrdConnected ∧ (0 : ℝ) ∈ J ∧ omIsUnitSpeedOn g δ J ∧ δ =ᶠ[nhds 0] ⇑α0
end MaximalCurve
section AbsorbMaximal
end AbsorbMaximal
section OntoMaximal
end OntoMaximal
section PeriodicCoincidence
end PeriodicCoincidence
section MinimalPeriod
end MinimalPeriod
section CircleExpLocalDiffeo
end CircleExpLocalDiffeo
section PeriodicCase
end PeriodicCase
section BoundaryInterior

/-- The inclusion of the open half of `H` into `E1`, as an open partial homeomorphism.
Its target is the interior of the range of `𝓡∂ 1`. -/
private def omb_interiorModelHomeomorph :
    OpenPartialHomeomorph (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1)) :=
  OpenPartialHomeomorph.mk
    (PartialHomeomorph.mk
      { toFun := Subtype.val
        invFun := (𝓡∂ 1).symm
        source := {y | 0 < (y.val) 0}
        target := {y | 0 < y 0}
        map_source' := fun _ hy => hy
        map_target' := by
          intro y hy
          have hy' : 0 < y.ofLp 0 := hy
          change 0 < (((𝓡∂ 1).symm y).val) 0
          rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le (le_of_lt hy')]
          exact hy'
        left_inv' := by
          intro y _
          exact ModelWithCorners.left_inv (𝓡∂ 1) y
        right_inv' := by
          intro y hy
          have hy' : 0 < y.ofLp 0 := hy
          have hle : 0 ≤ y.ofLp 0 := le_of_lt hy'
          have hmem : y ∈ Set.range (𝓡∂ 1) := by
            rw [range_modelWithCornersEuclideanHalfSpace]
            exact hle
          have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
          simpa using h }
      (continuous_subtype_val.continuousOn)
      ((ModelWithCorners.continuous_symm (𝓡∂ 1)).continuousOn))
    ((PiLp.continuous_apply 2 _ 0 |>.comp continuous_subtype_val).isOpen_preimage _
      isOpen_Ioi)
    ((PiLp.continuous_apply 2 _ 0).isOpen_preimage _ isOpen_Ioi)

/-- The interior of `M` as an open subset. -/
private def ombInterior : TopologicalSpace.Opens M :=
  ⟨(𝓡∂ 1).interior M, (𝓡∂ 1).isOpen_interior (by simp : (∞ : ℕ∞ω) ≠ 0)⟩

private theorem omb_mem_ombInterior_iff (x : M) :
    x ∈ ombInterior M ↔ (𝓡∂ 1).IsInteriorPoint x :=
  Iff.rfl

/-- The interior carries `E1` charts: the `H` chart followed by `ι`. -/
private instance ombChartedSpaceInterior :
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

/-- Every `E1` atlas member is a translated `H` chart. -/
private theorem omb_atlas_mem_obtain
    (e : OpenPartialHomeomorph ↥(ombInterior M) (EuclideanSpace ℝ (Fin 1)))
    (he : e ∈ atlas (EuclideanSpace ℝ (Fin 1)) ↥(ombInterior M)) :
    ∃ x : ↥(ombInterior M),
      (chartAt (EuclideanHalfSpace 1) x).trans omb_interiorModelHomeomorph = e :=
  he

/-- The transition between translated charts equals the `𝓡∂ 1` extended
coordinate change. -/
private theorem omb_trans_eq_extendCoordChange (x x' : ↥(ombInterior M)) :
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

/-- The interior is a boundaryless `E1` manifold. -/
private instance ombIsManifoldInterior :
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

/-- Retraction from `M` onto the interior subtype, defaulting to `x₀` outside. -/
private def ombRetract (x₀ : ↥(ombInterior M)) : M → ↥(ombInterior M) := by
  classical
  exact fun y => if h : y ∈ ombInterior M then ⟨y, h⟩ else x₀

/-- The half-chart curve at a boundary point: the chart inverse applied to the
ray `t ↦ t` in the model. -/
private def ombHalfCurve (p : M) : ℝ → M :=
  fun t => (chartAt (EuclideanHalfSpace 1) p).symm ((𝓡∂ 1).symm (omLinEquiv t))

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- At a boundary point, the chart sends `p` to the corner `0`. -/
private theorem omb_chartAt_boundary_val (p : M)
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
private theorem omb_symm_ray_zero (p : M)
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
private theorem omb_halfCurve_zero (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) : ombHalfCurve M p 0 = p := by
  simp only [ombHalfCurve]
  rw [omb_symm_ray_zero M p hp]
  exact (chartAt (EuclideanHalfSpace 1) p).left_inv (mem_chart_source _ p)

/-- Good radius bundle for the half-chart curve at `p`. -/
private def ombGoodRadius (p : M) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧
    ∀ t : ℝ, |t| < ε → (𝓡∂ 1).symm (omLinEquiv t) ∈
      (chartAt (EuclideanHalfSpace 1) p).target

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Radius on which the model ray stays in the chart target. -/
private theorem omb_exists_halfCurve_radius (p : M)
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
private theorem ombLinEquiv_coord (t : ℝ) : (omLinEquiv t).ofLp 0 = t := rfl

/-- For `t ≥ 0`, the model ray lands on the coercion. -/
private theorem omb_symm_ray_val_of_nonneg (t : ℝ) (ht : 0 ≤ t) :
    (((𝓡∂ 1).symm (omLinEquiv t)).val : EuclideanSpace ℝ (Fin 1)) =
      omLinEquiv t := by
  have hle : 0 ≤ (omLinEquiv t).ofLp 0 := by
    rw [ombLinEquiv_coord t]
    exact ht
  rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hle]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve is continuous on the symmetric interval. -/
private theorem omb_halfCurve_continuousOn (p : M) (ε : ℝ)
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
private theorem omb_halfCurve_tendsto (p : M)
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
private theorem omb_E1_ext {v w : EuclideanSpace ℝ (Fin 1)}
    (h : v.ofLp 0 = w.ofLp 0) : v = w := by
  apply PiLp.ext
  intro i
  fin_cases i
  simpa using h

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Image of the half-chart curve on an initial interval. -/
private theorem omb_halfCurve_image_Ico (p : M) (ε δ : ℝ)
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
private theorem omb_halfCurve_mem_interior (p : M) (ε t : ℝ)
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
private theorem omb_boundary_not_mem_interior (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) : p ∉ ombInterior M := by
  rw [omb_mem_ombInterior_iff]
  have h := (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint p).mp hp
  exact h

/-- Model identity: the ray meets the left Icc chart. -/
private theorem omb_symm_leftChart (z : Set.Icc (0 : ℝ) 1) :
    (𝓡∂ 1).symm (omLinEquiv z.val) = IccLeftChart 0 1 z := by
  have hnonneg : 0 ≤ (z.val : ℝ) := z.property.1
  apply EuclideanHalfSpace.ext
  rw [omb_symm_ray_val_of_nonneg _ hnonneg]
  apply omb_E1_ext
  rw [ombLinEquiv_coord, IccLeftChart_apply]
  simp

/-- Model identity: the ray meets the right Icc chart. -/
private theorem omb_symm_rightChart (z : Set.Icc (0 : ℝ) 1) :
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
private theorem omb_halfCurve_leftChart (p : M) (z : Set.Icc (0 : ℝ) 1) :
    ombHalfCurve M p z.val =
      (chartAt (EuclideanHalfSpace 1) p).symm (IccLeftChart 0 1 z) := by
  simp only [ombHalfCurve, omb_symm_leftChart]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The reflected half-chart curve meets the right Icc chart. -/
private theorem omb_halfCurve_rightChart (p : M) (z : Set.Icc (0 : ℝ) 1) :
    ombHalfCurve M p (1 - z.val) =
      (chartAt (EuclideanHalfSpace 1) p).symm (IccRightChart 0 1 z) := by
  simp only [ombHalfCurve, omb_symm_rightChart]

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The inverse of the half-chart curve reads off the model coordinate. -/
private def ombHalfCurveInv (p : M) : M → ℝ :=
  fun y => omLinEquiv.symm ((𝓡∂ 1) ((chartAt (EuclideanHalfSpace 1) p) y))

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve maps the open interval into the target box. -/
private theorem omb_halfCurve_maps_fwd (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    Set.MapsTo (ombHalfCurve M p) (Set.Ioo 0 ε)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
  intro t ht
  rw [Set.mem_Ioo] at ht
  have htabs : |t| < ε := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have hT := hε.2.2 t htabs
  have hsrc : ombHalfCurve M p t ∈ (chartAt (EuclideanHalfSpace 1) p).source := by
    simp only [ombHalfCurve]
    exact (chartAt (EuclideanHalfSpace 1) p).map_target hT
  refine ⟨hsrc, ?_⟩
  have hchart : (chartAt (EuclideanHalfSpace 1) p) (ombHalfCurve M p t) =
      (𝓡∂ 1).symm (omLinEquiv t) := by
    simp only [ombHalfCurve]
    exact (chartAt (EuclideanHalfSpace 1) p).right_inv hT
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hchart, omb_symm_ray_val_of_nonneg t ht.1.le, ombLinEquiv_coord]
  exact ht

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The coordinate map is a left inverse on the open interval. -/
private theorem omb_halfCurve_left_inv (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    ombHalfCurveInv M p (ombHalfCurve M p t) = t := by
  rw [Set.mem_Ioo] at ht
  have htabs : |t| < ε := by
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have hT := hε.2.2 t htabs
  simp only [ombHalfCurveInv, ombHalfCurve,
    (chartAt (EuclideanHalfSpace 1) p).right_inv hT]
  have hmem : omLinEquiv t ∈ Set.range (𝓡∂ 1) := by
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (omLinEquiv t).ofLp 0
    rw [ombLinEquiv_coord]
    exact ht.1.le
  have h := ModelWithCorners.right_inv (𝓡∂ 1) hmem
  have h2 : (𝓡∂ 1) ((𝓡∂ 1).symm (omLinEquiv t)) = omLinEquiv t := h
  rw [h2]
  exact omLinEquiv.symm_apply_apply t

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart curve is a right inverse on the target box. -/
private theorem omb_halfCurve_right_inv (p : M) (ε : ℝ)
    (y : M) (hy : y ∈ (chartAt (EuclideanHalfSpace 1) p).source ∩
      (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
        {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) :
    ombHalfCurve M p (ombHalfCurveInv M p y) = y := by
  obtain ⟨hxsrc, hxmem⟩ := hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hxmem
  have hcoord0 : 0 < ((((chartAt (EuclideanHalfSpace 1) p) y).val)).ofLp 0 :=
    hxmem.1
  have hcoordε : ((((chartAt (EuclideanHalfSpace 1) p) y).val)).ofLp 0 < ε :=
    hxmem.2
  set s : ℝ := ombHalfCurveInv M p y with hs
  have hval : omLinEquiv s =
      (((chartAt (EuclideanHalfSpace 1) p) y).val :
        EuclideanSpace ℝ (Fin 1)) := by
    rw [hs]
    simp only [ombHalfCurveInv]
    exact ContinuousLinearEquiv.apply_symm_apply omLinEquiv _
  have hspos : 0 ≤ s := by
    have : s = (omLinEquiv s).ofLp 0 := (ombLinEquiv_coord s).symm
    rw [this, hval]
    exact hcoord0.le
  have hH : (𝓡∂ 1).symm (omLinEquiv s) =
      (chartAt (EuclideanHalfSpace 1) p) y := by
    apply EuclideanHalfSpace.ext
    rw [omb_symm_ray_val_of_nonneg s hspos, hval]
  simp only [ombHalfCurve, hH]
  exact (chartAt (EuclideanHalfSpace 1) p).left_inv hxsrc

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The coordinate map lands in the open interval. -/
private theorem omb_halfCurveInv_maps (p : M) (ε : ℝ) :
    Set.MapsTo (ombHalfCurveInv M p)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε})
      (Set.Ioo 0 ε) := by
  intro y hy
  obtain ⟨-, hxmem⟩ := hy
  simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hxmem
  have hval : omLinEquiv (ombHalfCurveInv M p y) =
      (((chartAt (EuclideanHalfSpace 1) p) y).val :
        EuclideanSpace ℝ (Fin 1)) := by
    simp only [ombHalfCurveInv]
    exact ContinuousLinearEquiv.apply_symm_apply omLinEquiv _
  have hcoord : ombHalfCurveInv M p y =
      ((((chartAt (EuclideanHalfSpace 1) p) y).val)).ofLp 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v.ofLp 0) hval
    simpa [ombLinEquiv_coord] using h
  rw [Set.mem_Ioo, hcoord]
  exact hxmem

/-- The half-chart curve is smooth on the open interval. -/
private theorem omb_halfCurve_contMDiffOn (p : M) (ε : ℝ)
    (hε : ombGoodRadius M p ε) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) (Set.Ioo 0 ε) := by
  have h1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ omLinEquiv :=
    contMDiff_iff_contDiff.mpr omLinEquiv.contDiff
  have h1On : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
      omLinEquiv (Set.Ioo 0 ε) := h1.contMDiffOn
  have hmaps1 : Set.Ioo 0 ε ⊆ omLinEquiv ⁻¹' Set.range (𝓡∂ 1) := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    rw [Set.mem_preimage, range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ (omLinEquiv t).ofLp 0
    rw [ombLinEquiv_coord]
    exact ht.1.le
  have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ 1) ∞
      (𝓡∂ 1).symm (Set.range (𝓡∂ 1)) :=
    (𝓡∂ 1).contMDiffOn_symm
  have h12 : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞
      ((𝓡∂ 1).symm ∘ omLinEquiv) (Set.Ioo 0 ε) := h2.comp h1On hmaps1
  have hmaps2 : Set.Ioo 0 ε ⊆ ((𝓡∂ 1).symm ∘ omLinEquiv) ⁻¹'
      (chartAt (EuclideanHalfSpace 1) p).target := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    simp only [Set.mem_preimage, Function.comp_apply]
    apply hε.2.2
    rw [abs_of_nonneg ht.1.le]
    exact ht.2
  have h3 : ContMDiffOn (𝓡∂ 1) (𝓡∂ 1) ∞
      (chartAt (EuclideanHalfSpace 1) p).symm
      (chartAt (EuclideanHalfSpace 1) p).target :=
    contMDiffOn_chart_symm
  have hfin : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞
      ((chartAt (EuclideanHalfSpace 1) p).symm ∘
        ((𝓡∂ 1).symm ∘ omLinEquiv)) (Set.Ioo 0 ε) := h3.comp h12 hmaps2
  have heq : ombHalfCurve M p =
      (chartAt (EuclideanHalfSpace 1) p).symm ∘
        ((𝓡∂ 1).symm ∘ omLinEquiv) := rfl
  rw [heq]
  exact hfin

/-- The half-chart curve is a local diffeomorphism on the open interval. -/
private theorem omb_isLocalDiffeomorphAt_halfCurve (p : M) (ε t : ℝ)
    (hε : ombGoodRadius M p ε) (ht : t ∈ Set.Ioo 0 ε) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) t := by
  have hInv : Set.InvOn (ombHalfCurveInv M p) (ombHalfCurve M p)
      (Set.Ioo 0 ε)
      ((chartAt (EuclideanHalfSpace 1) p).source ∩
        (chartAt (EuclideanHalfSpace 1) p) ⁻¹'
          {y : EuclideanHalfSpace 1 | 0 < (y.val) 0 ∧ (y.val) 0 < ε}) := by
    refine ⟨?_, ?_⟩
    · intro s hs
      exact omb_halfCurve_left_inv M p ε hε s hs
    · intro y hy
      exact omb_halfCurve_right_inv M p ε y hy
  exact odm_isLocalDiffeomorphAt_of_invOn _ _ _ _ isOpen_Ioo
    (omb_halfCurve_V_open M p ε) (omb_halfCurve_maps_fwd M p ε hε)
    (omb_halfCurveInv_maps M p ε) hInv
    (omb_halfCurve_contMDiffOn M p ε hε)
    (omb_halfCurveInv_contMDiffOn M p ε) t ht

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- The half-chart image on an initial interval is open. -/
private theorem omb_halfCurve_image_open (p : M) (ε δ : ℝ)
    (hε : ombGoodRadius M p ε) (hδε : δ ≤ ε) :
    IsOpen ((ombHalfCurve M p) '' Set.Ico 0 δ) := by
  rw [omb_halfCurve_image_Ico M p ε δ hε hδε]
  apply (chartAt (EuclideanHalfSpace 1) p).isOpen_inter_preimage
  have hcont : Continuous
      (fun y : EuclideanHalfSpace 1 => ((y.val).ofLp 0 : ℝ)) :=
    ((PiLp.continuous_apply 2 _ 0).comp continuous_subtype_val)
  have : {y : EuclideanHalfSpace 1 | (y.val).ofLp 0 < δ} =
      (fun y : EuclideanHalfSpace 1 => ((y.val).ofLp 0 : ℝ)) ⁻¹' Set.Iio δ :=
    rfl
  rw [this]
  exact isOpen_Iio.preimage hcont

/-- The interior is nonempty. -/
private theorem omb_nonempty_ombInterior [ConnectedSpace M] :
    (ombInterior M : Set M).Nonempty := by
  obtain ⟨x⟩ := (inferInstance : Nonempty M)
  rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x with h | h
  · exact ⟨x, (omb_mem_ombInterior_iff M x).mpr h⟩
  · obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M x h
    refine ⟨ombHalfCurve M x (ε / 2), ?_⟩
    have hmem : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := by
      rw [Set.mem_Ioo]
      constructor <;> linarith [hε.1]
    have h := omb_halfCurve_mem_interior M x ε (ε / 2) hε hmem
    exact SetLike.mem_coe.mp h

/-- The interior is dense. -/
private theorem omb_closure_ombInterior [ConnectedSpace M] :
    closure (ombInterior M : Set M) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x with h | h
  · exact subset_closure (SetLike.mem_coe.mp ((omb_mem_ombInterior_iff M x).mpr h))
  · obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M x h
    apply mem_closure_of_tendsto
      (omb_halfCurve_tendsto M x h ε hε)
    filter_upwards [Ioo_mem_nhdsGT hε.1] with t ht
    have hmem : t ∈ Set.Ioo (0 : ℝ) ε := ht
    have h := omb_halfCurve_mem_interior M x ε t hε hmem
    exact SetLike.mem_coe.mp h

/-- Each boundary tail lies on one side of a disjoint cover of the interior. -/
private theorem omb_tail_side [ConnectedSpace M]
    (u v : Set M) (hu : IsOpen u) (hv : IsOpen v)
    (hcover : (ombInterior M : Set M) ⊆ u ∪ v)
    (hdisj : (ombInterior M : Set M) ∩ (u ∩ v) = ∅)
    (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    ∃ ε, ombGoodRadius M p ε ∧
      ((ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u ∨
        (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ v) := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M p hp
  refine ⟨ε, hε, ?_⟩
  have hsub : Set.Ioo (0 : ℝ) ε ⊆ Set.Ioo (-ε) ε :=
    Set.Ioo_subset_Ioo (by linarith [hε.1]) le_rfl
  have hpre : IsPreconnected ((ombHalfCurve M p) '' Set.Ioo 0 ε) :=
    isPreconnected_Ioo.image _
      ((omb_halfCurve_continuousOn M p ε hε).mono hsub)
  have hTS : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ (ombInterior M : Set M) := by
    rintro y ⟨t, ht, rfl⟩
    exact SetLike.mem_coe.mp (omb_halfCurve_mem_interior M p ε t hε ht)
  have hTuv : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u ∪ v :=
    hTS.trans hcover
  have hTdisj : (ombHalfCurve M p) '' Set.Ioo 0 ε ∩ (u ∩ v) = ∅ := by
    have hsub2 : (ombHalfCurve M p) '' Set.Ioo 0 ε ∩ (u ∩ v) ⊆
        (ombInterior M : Set M) ∩ (u ∩ v) :=
      Set.inter_subset_inter hTS le_rfl
    rw [hdisj] at hsub2
    exact Set.subset_empty_iff.mp hsub2
  exact (isPreconnected_iff_subset_of_disjoint.mp hpre) u v hu hv hTuv hTdisj

/-- A cap meets the interior only along its tail. -/
private theorem omb_cap_inter_subset (p : M)
    (hp : (𝓡∂ 1).IsBoundaryPoint p) (ε δ : ℝ)
    (hδε : δ ≤ ε) (u : Set M)
    (htail : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u) :
    ((ombHalfCurve M p) '' Set.Ico 0 δ) ∩ (ombInterior M : Set M) ⊆ u := by
  rintro x ⟨⟨t, ⟨ht0, htδ⟩, rfl⟩, hxS⟩
  rcases eq_or_lt_of_le ht0 with h0 | hpos
  · subst h0
    rw [omb_halfCurve_zero M p hp] at hxS
    exact absurd (SetLike.mem_coe.mpr hxS)
      (omb_boundary_not_mem_interior M p hp)
  · apply htail
    refine ⟨t, ?_, rfl⟩
    rw [Set.mem_Ioo]
    exact ⟨hpos, lt_of_lt_of_le htδ hδε⟩

/-- Cap union on one side of a cover of the interior. -/
private def ombSideCap (u : Set M) : Set M :=
  u ∪ ⋃ (p : M) (_ : (𝓡∂ 1).IsBoundaryPoint p) (ε : ℝ)
    (_ : ombGoodRadius M p ε)
    (_ : (ombHalfCurve M p) '' Set.Ioo 0 ε ⊆ u),
    (ombHalfCurve M p) '' Set.Ico 0 ε

omit [IsManifold (𝓡∂ 1) ∞ M] in
/-- Each cap in the union is open. -/
private theorem omb_sideCap_open (u : Set M) (hu : IsOpen u) :
    IsOpen (ombSideCap M u) := by
  unfold ombSideCap
  apply hu.union
  apply isOpen_iUnion; intro p
  apply isOpen_iUnion; intro _
  apply isOpen_iUnion; intro ε
  apply isOpen_iUnion; intro hε
  apply isOpen_iUnion; intro _
  exact omb_halfCurve_image_open M p ε ε hε le_rfl

/-- Points of the interior in a side cap lie in the side. -/
private theorem omb_mem_of_sideCap_inter (u : Set M)
    (x : M) (hxS : x ∈ (ombInterior M : Set M)) (hx : x ∈ ombSideCap M u) :
    x ∈ u := by
  unfold ombSideCap at hx
  rcases hx with h | h
  · exact h
  · simp only [Set.mem_iUnion] at h
    obtain ⟨p, hp, ε, hε, htail, hcap⟩ := h
    exact omb_cap_inter_subset M p hp ε ε le_rfl u htail ⟨hcap, hxS⟩

/-- The interior is preconnected. -/
private theorem omb_isPreconnected_ombInterior [ConnectedSpace M] :
    IsPreconnected (ombInterior M : Set M) := by
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv hcover hdisj
  have hU'open : IsOpen (ombSideCap M u) := omb_sideCap_open M u hu
  have hV'open : IsOpen (ombSideCap M v) := omb_sideCap_open M v hv
  have hSU : ∀ x ∈ (ombInterior M : Set M), x ∈ ombSideCap M u → x ∈ u :=
    fun x hxS hx => omb_mem_of_sideCap_inter M u x hxS hx
  have hSV : ∀ x ∈ (ombInterior M : Set M), x ∈ ombSideCap M v → x ∈ v :=
    fun x hxS hx => omb_mem_of_sideCap_inter M v x hxS hx
  have hdisj' : ombSideCap M u ∩ ombSideCap M v ∩ (ombInterior M : Set M) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨hxU, hxV⟩, hxS⟩
    have hxu := hSU x hxS hxU
    have hxv := hSV x hxS hxV
    have hmem : x ∈ (ombInterior M : Set M) ∩ (u ∩ v) := ⟨hxS, hxu, hxv⟩
    rw [hdisj] at hmem
    exact Set.notMem_empty x hmem
  have hUV : ombSideCap M u ∩ ombSideCap M v = ∅ := by
    by_contra hne
    have hne' : (ombSideCap M u ∩ ombSideCap M v).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have hdense : Dense (ombInterior M : Set M) :=
      dense_iff_closure_eq.mpr (omb_closure_ombInterior M)
    obtain ⟨y, hyUV, hyS⟩ :=
      (dense_iff_inter_open.mp hdense) _ (hU'open.inter hV'open) hne'
    have hmem : y ∈ ombSideCap M u ∩ ombSideCap M v ∩ (ombInterior M : Set M) :=
      ⟨hyUV, hyS⟩
    rw [hdisj'] at hmem
    exact Set.notMem_empty y hmem
  have hcoverM : (Set.univ : Set M) ⊆ ombSideCap M u ∪ ombSideCap M v := by
    intro x _
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) x
      with h | h
    · have hxS : x ∈ (ombInterior M : Set M) :=
        SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M x).mpr h)
      rcases hcover hxS with hxu | hxv
      · exact Or.inl (Or.inl hxu)
      · exact Or.inr (Or.inl hxv)
    · obtain ⟨ε, hε, hside⟩ := omb_tail_side M u v hu hv hcover hdisj x h
      rcases hside with htail | htail
      · refine Or.inl (Or.inr ?_)
        simp only [Set.mem_iUnion]
        exact ⟨x, h, ε, hε, htail, 0, ⟨le_rfl, hε.1⟩,
          omb_halfCurve_zero M x h⟩
      · refine Or.inr (Or.inr ?_)
        simp only [Set.mem_iUnion]
        exact ⟨x, h, ε, hε, htail, 0, ⟨le_rfl, hε.1⟩,
          omb_halfCurve_zero M x h⟩
  have hUVdisj : (Set.univ : Set M) ∩ (ombSideCap M u ∩ ombSideCap M v) = ∅ := by
    rw [Set.univ_inter]
    exact hUV
  rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_univ)
    _ _ hU'open hV'open hcoverM hUVdisj with hU | hV
  · exact Or.inl (fun x hxS => hSU x hxS (hU (Set.mem_univ x)))
  · exact Or.inr (fun x hxS => hSV x hxS (hV (Set.mem_univ x)))

/-- The interior is connected. -/
private instance omb_connectedSpace_ombInterior [ConnectedSpace M] :
    ConnectedSpace ↥(ombInterior M) :=
  isConnected_iff_connectedSpace.mp
    ⟨omb_nonempty_ombInterior M, omb_isPreconnected_ombInterior M⟩

end BoundaryInterior

end MathlibExt.Geometry.Manifold.OneDimensionalClassification

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

open MathlibExt.Geometry.Manifold.OneDimensionalClassification

/-- Empty boundary: `M` is diffeomorphic to `Circle`. -/
private theorem omb_circle_of_boundary_empty (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : ModelWithCorners.boundary (I := 𝓡∂ 1) M = ∅) :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) := by
  have hS : ((ombInterior M : TopologicalSpace.Opens M) : Set M) = Set.univ := by
    have h := ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 1) (M := M)
    rw [hB, Set.union_empty] at h
    exact h
  obtain ⟨xw, hxw⟩ := omb_nonempty_ombInterior M
  let x₀ : ↥(ombInterior M) := ⟨xw, hxw⟩
  have hbij : Function.Bijective (Subtype.val : ↥(ombInterior M) → M) := by
    refine ⟨Subtype.val_injective, ?_⟩
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    show y ∈ ombInterior M
    have hy : y ∈ ((ombInterior M : TopologicalSpace.Opens M) : Set M) := by
      rw [hS]
      exact Set.mem_univ y
    exact hy
  have hld := omb_isLocalDiffeomorph_val M x₀
  have hD : Nonempty (↥(ombInterior M) ≃ₘ⟮𝓡 1, 𝓡∂ 1⟯ M) :=
    ⟨hld.diffeomorphOfBijective hbij⟩
  obtain ⟨D⟩ := hD
  rcases omb_blackbox_interior M with ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩
  · exact ⟨D.symm.trans Φ⟩
  · have DE : M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ EuclideanSpace ℝ (Fin 1) := D.symm.trans Φ
    have hC := Homeomorph.compactSpace DE.toHomeomorph
    exact absurd (@isCompact_univ _ _ hC) (noncompact_univ _)

/-- Nonempty boundary: the interior is diffeomorphic to `ℝ`. -/
private theorem omb_exists_diffeomorph_real_interior (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    Nonempty (ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) := by
  rcases omb_blackbox_interior M with ⟨⟨Φ⟩⟩ | ⟨⟨Φ⟩⟩
  · have hC := Homeomorph.compactSpace Φ.toHomeomorph.symm
    have hcpt : IsCompact ((ombInterior M : TopologicalSpace.Opens M) : Set M) :=
      isCompact_iff_compactSpace.mpr hC
    have hclopen : IsClopen ((ombInterior M : TopologicalSpace.Opens M) : Set M) :=
      ⟨hcpt.isClosed, (ombInterior M).2⟩
    have huniv := hclopen.eq_univ (omb_nonempty_ombInterior M)
    obtain ⟨p, hp⟩ := hB
    have hpS : p ∈ ((ombInterior M : TopologicalSpace.Opens M) : Set M) := by
      rw [huniv]
      exact Set.mem_univ p
    have hmem := (omb_mem_ombInterior_iff M p).mp hpS
    have hbp : (𝓡∂ 1).IsBoundaryPoint p := hp
    exact ((𝓡∂ 1).isBoundaryPoint_iff_not_isInteriorPoint p).mp hbp hmem |>.elim
  · exact ⟨omLinEquiv.toDiffeomorph.trans Φ.symm⟩

/-- The end map: `Ψ.symm` of the retracted half-curve. -/
private def ombTheta (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) : ℝ → ℝ :=
  fun t => Ψ.symm (ombRetract M x₀ (ombHalfCurve M p t))

/-- On the tail, `Ψ (θ t)` recovers the half-curve. -/
private theorem omb_theta_apply (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    ((Ψ (ombTheta M Ψ x₀ p t) : ↥(ombInterior M)) : M)
      = ombHalfCurve M p t := by
  have hmemO : ombHalfCurve M p t ∈ ombInterior M :=
    omb_halfCurve_mem_interior M p ε t hε ht
  have e : ombTheta M Ψ x₀ p t
      = Ψ.symm (ombRetract M x₀ (ombHalfCurve M p t)) := rfl
  rw [e, Ψ.apply_symm_apply, ombRetract_of_mem M x₀ _ hmemO]

/-- The end map is a local diffeomorphism on the tail. -/
private theorem omb_isLocalDiffeomorphAt_theta (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (ombTheta M Ψ x₀ p) t := by
  have h1 : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ (ombHalfCurve M p) t :=
    omb_isLocalDiffeomorphAt_halfCurve M p ε t hε ht
  have hmem : ombHalfCurve M p t ∈ (ombInterior M : Set M) :=
    SetLike.mem_coe.mp (omb_halfCurve_mem_interior M p ε t hε ht)
  have h2 : IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡 1) ∞ (ombRetract M x₀)
      (ombHalfCurve M p t) :=
    omb_isLocalDiffeomorphAt_retract M x₀ _ hmem
  have h3 : IsLocalDiffeomorphAt (𝓡 1) 𝓘(ℝ, ℝ) ∞ (⇑Ψ.symm)
      (ombRetract M x₀ (ombHalfCurve M p t)) :=
    Ψ.symm.isLocalDiffeomorph _
  have h12 := IsLocalDiffeomorphAt.comp (K := (𝓡 1)) (P := ↥(ombInterior M)) h1 h2
  have h := IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) h12 h3
  have e : (⇑Ψ.symm ∘ ombRetract M x₀ ∘ ombHalfCurve M p)
      = ombTheta M Ψ x₀ p := rfl
  rw [e] at h
  exact h

/-- The end map is smooth on the tail interval. -/
private theorem omb_theta_contDiffOn (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) :
    ContDiffOn ℝ ∞ (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
  intro t ht
  have h := omb_isLocalDiffeomorphAt_theta M Ψ x₀ p ε hε t ht
  exact h.contMDiffAt.contDiffAt.contDiffWithinAt

/-- The derivative of the end map never vanishes on the tail. -/
private theorem omb_theta_deriv_ne (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) (t : ℝ) (ht : t ∈ Set.Ioo 0 ε) :
    deriv (ombTheta M Ψ x₀ p) t ≠ 0 := by
  have h := omb_isLocalDiffeomorphAt_theta M Ψ x₀ p ε hε t ht
  have hinv := h.isInvertible_mfderiv (by simp : (∞ : ℕ∞ω) ≠ 0)
  have heq : (fderiv ℝ (ombTheta M Ψ x₀ p) t)
      = (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (ombTheta M Ψ x₀ p) t) :=
    mfderiv_eq_fderiv.symm
  have hinv2 : (fderiv ℝ (ombTheta M Ψ x₀ p) t).IsInvertible := heq ▸ hinv
  obtain ⟨A, hA⟩ := hinv2
  have h1 : (fderiv ℝ (ombTheta M Ψ x₀ p) t) 1 ≠ 0 := by
    rw [← hA]
    have hA1 : A (1 : ℝ) ≠ A 0 := by
      intro hcon
      exact one_ne_zero (A.injective hcon)
    rwa [map_zero] at hA1
  rwa [fderiv_apply_one_eq_deriv] at h1

/-- The derivative of the end map has constant sign on the tail. -/
private theorem omb_theta_deriv_sign (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M)
    (ε : ℝ) (hε : ombGoodRadius M p ε) :
    (∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t) ∨
      (∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0) := by
  have hne : ∀ t ∈ Set.Ioo (0 : ℝ) ε, deriv (ombTheta M Ψ x₀ p) t ≠ 0 :=
    fun t ht => omb_theta_deriv_ne M Ψ x₀ p ε hε t ht
  have hcont : ContinuousOn (deriv (ombTheta M Ψ x₀ p)) (Set.Ioo 0 ε) :=
    (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn_deriv_of_isOpen isOpen_Ioo
      (by simp : (1 : ℕ∞ω) ≤ ∞)
  by_cases h : ∃ t ∈ Set.Ioo (0 : ℝ) ε, 0 < deriv (ombTheta M Ψ x₀ p) t
  · left
    obtain ⟨a, ha, hapos⟩ := h
    intro t ht
    rcases lt_trichotomy (deriv (ombTheta M Ψ x₀ p) t) 0 with hneg | hzero | hpos
    · exfalso
      obtain ⟨c, hc, hczero⟩ := isPreconnected_Ioo.intermediate_value₂ ht ha
        hcont continuousOn_const (le_of_lt hneg) (le_of_lt hapos)
      exact hne c hc hczero
    · exact absurd hzero (hne t ht)
    · exact hpos
  · right
    push Not at h
    intro t ht
    rcases lt_or_gt_of_ne (hne t ht) with hneg | hpos
    · exact hneg
    · have hle := h t ht
      linarith

/-- A two-sided bound on a tail interval is impossible. -/
private theorem omb_theta_bounded_false (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (δ : ℝ) (hδpos : 0 < δ) (hδε : δ ≤ ε) (lo hi : ℝ)
    (hb : ∀ t ∈ Set.Ioo (0 : ℝ) δ, ombTheta M Ψ x₀ p t ∈ Set.Icc lo hi) :
    False := by
  set K : Set M := (fun u : ℝ => ((Ψ u : ↥(ombInterior M)) : M)) ''
    Set.Icc lo hi with hKdef
  have hKc : IsCompact K := by
    rw [hKdef]
    apply IsCompact.image isCompact_Icc
    exact continuous_subtype_val.comp Ψ.continuous
  have hKclosed : IsClosed K := hKc.isClosed
  have hpclosure : p ∈ closure ((ombHalfCurve M p) '' Set.Ioo 0 δ) := by
    apply mem_closure_of_tendsto (omb_halfCurve_tendsto M p hp ε hε)
    filter_upwards [Ioo_mem_nhdsGT hδpos] with t ht
    exact ⟨t, ht, rfl⟩
  have hsub : (ombHalfCurve M p) '' Set.Ioo 0 δ ⊆ K := by
    rintro y ⟨t, ht, rfl⟩
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    have hθt := hb t ht
    rw [hKdef]
    exact ⟨ombTheta M Ψ x₀ p t, hθt,
      omb_theta_apply M Ψ x₀ p ε hε t htε⟩
  have hpK : p ∈ K := closure_minimal hsub hKclosed hpclosure
  obtain ⟨u, _, hpu⟩ := hpK
  have hpS : p ∈ (ombInterior M : Set M) := by
    rw [← hpu]
    exact (Ψ u).2
  have hnot : p ∉ ombInterior M := omb_boundary_not_mem_interior M p hp
  exact hnot (SetLike.mem_coe.mpr hpS)

/-- Increasing end map tends to `atBot`. -/
private theorem omb_theta_tendsto_atBot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hpos : ∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot := by
  have hmono : StrictMonoOn (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 ε)
      (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn
    rw [interior_Ioo]
    exact hpos
  rw [Filter.tendsto_atBot]
  intro B
  obtain ⟨t₀, ht₀, hlt⟩ :
      ∃ t ∈ Set.Ioo (0 : ℝ) ε, ombTheta M Ψ x₀ p t < B := by
    by_contra hcon
    push Not at hcon
    have hδpos : (0 : ℝ) < ε / 2 := by linarith [hε.1]
    have hδε : ε / 2 ≤ ε := by linarith [hε.1]
    have hδε' : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
    apply omb_theta_bounded_false M Ψ x₀ p hp ε hε (ε / 2) hδpos hδε B
      (ombTheta M Ψ x₀ p (ε / 2))
    intro t ht
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    refine ⟨hcon t htε, ?_⟩
    exact le_of_lt (hmono htε hδε' ht.2)
  filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
  have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_trans ht.2 ht₀.2⟩
  exact le_of_lt (lt_trans (hmono htε ht₀ ht.2) hlt)

/-- Decreasing end map tends to `atTop`. -/
private theorem omb_theta_tendsto_atTop (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hneg : ∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  have hanti : StrictAntiOn (ombTheta M Ψ x₀ p) (Set.Ioo 0 ε) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo 0 ε)
      (omb_theta_contDiffOn M Ψ x₀ p ε hε).continuousOn
    rw [interior_Ioo]
    exact hneg
  rw [Filter.tendsto_atTop]
  intro B
  obtain ⟨t₀, ht₀, hgt⟩ :
      ∃ t ∈ Set.Ioo (0 : ℝ) ε, B < ombTheta M Ψ x₀ p t := by
    by_contra hcon
    push Not at hcon
    have hδpos : (0 : ℝ) < ε / 2 := by linarith [hε.1]
    have hδε : ε / 2 ≤ ε := by linarith [hε.1]
    have hδε' : ε / 2 ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
    apply omb_theta_bounded_false M Ψ x₀ p hp ε hε (ε / 2) hδpos hδε
      (ombTheta M Ψ x₀ p (ε / 2)) B
    intro t ht
    have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_of_lt_of_le ht.2 hδε⟩
    refine ⟨?_, hcon t htε⟩
    exact le_of_lt (hanti htε hδε' ht.2)
  filter_upwards [Ioo_mem_nhdsGT ht₀.1] with t ht
  have htε : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht.1, lt_trans ht.2 ht₀.2⟩
  exact le_of_lt (lt_trans hgt (hanti htε ht₀ ht.2))

/-- The composite `val ∘ Ψ`, landing in the interior. -/
private def ombValPsi (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) : ℝ → M :=
  fun u => ((Ψ u : ↥(ombInterior M)) : M)

/-- A left end absorbs far-left values into any of its neighbourhoods. -/
private theorem omb_absorb_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x : M) (hx : (𝓡∂ 1).IsBoundaryPoint x)
    (ε : ℝ) (hε : ombGoodRadius M x ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atBot)
    (N : Set M) (hN : N ∈ 𝓝 x) :
    ∃ R, ∀ u < R, ombValPsi M Ψ u ∈ N := by
  obtain ⟨δ, hδpos, hδ⟩ := omb_eventually_nhdsGT_Ioo
    ((omb_halfCurve_tendsto M x hx ε hε).eventually hN)
  have hminpos : 0 < min δ ε := lt_min hδpos hε.1
  have hminε : min δ ε ≤ ε := min_le_right _ _
  have hminδ : min δ ε ≤ δ := min_le_left _ _
  have ht₀ε : min δ ε / 2 ∈ Set.Ioo (0 : ℝ) ε :=
    ⟨by linarith, by linarith⟩
  refine ⟨ombTheta M Ψ x₀ x (min δ ε / 2), ?_⟩
  intro u hu
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ombTheta M Ψ x₀ x t < u :=
    hlim.eventually (Filter.eventually_lt_atBot u)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (min δ ε / 2) :=
    Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < min δ ε / 2)
  obtain ⟨t₁, ht₁lt, ht₁mem⟩ := (hev1.and hev2).exists
  have ht₁ε : t₁ ∈ Set.Ioo (0 : ℝ) ε :=
    ⟨ht₁mem.1, lt_trans ht₁mem.2 (by linarith)⟩
  have hcont : ContinuousOn (ombTheta M Ψ x₀ x)
      (Set.Icc t₁ (min δ ε / 2)) :=
    (omb_theta_contDiffOn M Ψ x₀ x ε hε).continuousOn.mono (by
      intro t ht
      rw [Set.mem_Icc] at ht
      rw [Set.mem_Ioo]
      exact ⟨lt_of_lt_of_le ht₁mem.1 ht.1,
        lt_of_le_of_lt ht.2 (by linarith [hminpos, hminε])⟩)
  have hivt := intermediate_value_Icc (le_of_lt ht₁mem.2) hcont
  have hmem : u ∈ Set.Icc (ombTheta M Ψ x₀ x t₁)
      (ombTheta M Ψ x₀ x (min δ ε / 2)) :=
    ⟨le_of_lt ht₁lt, le_of_lt hu⟩
  obtain ⟨t, htIcc, htθ⟩ := hivt hmem
  have htδ : t ∈ Set.Ioo (0 : ℝ) (min δ ε) := by
    rw [Set.mem_Icc] at htIcc
    refine ⟨lt_of_lt_of_le ht₁mem.1 htIcc.1, ?_⟩
    calc t ≤ min δ ε / 2 := htIcc.2
      _ < min δ ε := by linarith [hminpos]
  have htN : ombHalfCurve M x t ∈ N := by
    apply hδ t
    rw [Set.mem_Ioo]
    exact ⟨htδ.1, lt_of_lt_of_le htδ.2 hminδ⟩
  have htu : t ∈ Set.Ioo (0 : ℝ) ε :=
    ⟨htδ.1, lt_of_lt_of_le htδ.2 hminε⟩
  have heq : ombValPsi M Ψ u = ombHalfCurve M x t := by
    have h1 : ombValPsi M Ψ (ombTheta M Ψ x₀ x t) = ombHalfCurve M x t :=
      omb_theta_apply M Ψ x₀ x ε hε t htu
    rw [← htθ]
    exact h1
  rw [heq]
  exact htN

/-- A right end absorbs far-right values into any of its neighbourhoods. -/
private theorem omb_absorb_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x : M) (hx : (𝓡∂ 1).IsBoundaryPoint x)
    (ε : ℝ) (hε : ombGoodRadius M x ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atTop)
    (N : Set M) (hN : N ∈ 𝓝 x) :
    ∃ R, ∀ u > R, ombValPsi M Ψ u ∈ N := by
  obtain ⟨δ, hδpos, hδ⟩ := omb_eventually_nhdsGT_Ioo
    ((omb_halfCurve_tendsto M x hx ε hε).eventually hN)
  have hminpos : 0 < min δ ε := lt_min hδpos hε.1
  have hminε : min δ ε ≤ ε := min_le_right _ _
  have hminδ : min δ ε ≤ δ := min_le_left _ _
  have hcontIoo := (omb_theta_contDiffOn M Ψ x₀ x ε hε).continuousOn
  have hsubIoo : ∀ t ∈ Set.Ioo (0 : ℝ) (min δ ε),
      ombHalfCurve M x t ∈ N := by
    intro t ht
    apply hδ t
    exact ⟨ht.1, lt_of_lt_of_le ht.2 hminδ⟩
  refine ⟨ombTheta M Ψ x₀ x (min δ ε / 2), ?_⟩
  intro u hu
  have hev1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), u < ombTheta M Ψ x₀ x t :=
    hlim.eventually (Filter.eventually_gt_atTop u)
  have hev2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (min δ ε) :=
    Ioo_mem_nhdsGT hminpos
  obtain ⟨t₁, ht₁gt, ht₁mem⟩ := (hev1.and hev2).exists
  have hmemIcc : u ∈ Set.Icc (ombTheta M Ψ x₀ x (min δ ε / 2))
      (ombTheta M Ψ x₀ x t₁) :=
    ⟨le_of_lt hu, le_of_lt ht₁gt⟩
  rcases le_total (min δ ε / 2) t₁ with hle | hle
  · obtain ⟨t, htIcc, htθ⟩ := intermediate_value_Icc hle
      (hcontIoo.mono (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le (by linarith [hminpos]) ht.1,
          lt_of_le_of_lt ht.2 (lt_of_lt_of_le ht₁mem.2 hminε)⟩)) hmemIcc
    have ht0 : 0 < t := lt_of_lt_of_le (by linarith) htIcc.1
    have htmin : t < min δ ε := lt_of_le_of_lt htIcc.2 ht₁mem.2
    have htN : ombHalfCurve M x t ∈ N := hsubIoo t ⟨ht0, htmin⟩
    have htu : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht0, lt_of_lt_of_le htmin hminε⟩
    have heq : ombValPsi M Ψ u = ombHalfCurve M x t := by
      have h1 : ombValPsi M Ψ (ombTheta M Ψ x₀ x t) = ombHalfCurve M x t :=
        omb_theta_apply M Ψ x₀ x ε hε t htu
      rw [← htθ]
      exact h1
    rw [heq]
    exact htN
  · obtain ⟨t, htIcc, htθ⟩ := intermediate_value_Icc' hle
      (hcontIoo.mono (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [Set.mem_Ioo]
        exact ⟨lt_of_lt_of_le ht₁mem.1 ht.1,
          lt_of_le_of_lt ht.2 (by linarith [hminpos, hminε])⟩)) hmemIcc
    have ht0 : 0 < t := lt_of_lt_of_le ht₁mem.1 htIcc.1
    have htmin : t < min δ ε := by
      calc t ≤ min δ ε / 2 := htIcc.2
        _ < min δ ε := by linarith [hminpos]
    have htN : ombHalfCurve M x t ∈ N := hsubIoo t ⟨ht0, htmin⟩
    have htu : t ∈ Set.Ioo (0 : ℝ) ε := ⟨ht0, lt_of_lt_of_le htmin hminε⟩
    have heq : ombValPsi M Ψ u = ombHalfCurve M x t := by
      have h1 : ombValPsi M Ψ (ombTheta M Ψ x₀ x t) = ombHalfCurve M x t :=
        omb_theta_apply M Ψ x₀ x ε hε t htu
      rw [← htθ]
      exact h1
    rw [heq]
    exact htN

/-- Every boundary point is a left end or a right end. -/
private theorem omb_theta_tendsto (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p) :
    Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot ∨
      Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M p hp
  rcases omb_theta_deriv_sign M Ψ x₀ p ε hε with hpos | hneg
  · exact Or.inl (omb_theta_tendsto_atBot M Ψ x₀ p hp ε hε hpos)
  · exact Or.inr (omb_theta_tendsto_atTop M Ψ x₀ p hp ε hε hneg)

/-- Two left ends coincide. -/
private theorem omb_end_unique_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x y : M)
    (hx : (𝓡∂ 1).IsBoundaryPoint x) (hy : (𝓡∂ 1).IsBoundaryPoint y)
    (hlimx : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atBot)
    (hlimy : Filter.Tendsto (ombTheta M Ψ x₀ y) (𝓝[>] 0) Filter.atBot) :
    x = y := by
  by_contra hne
  obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hdisj⟩ := t2_separation hne
  obtain ⟨εx, hεx⟩ := omb_exists_halfCurve_radius M x hx
  obtain ⟨εy, hεy⟩ := omb_exists_halfCurve_radius M y hy
  obtain ⟨R₁, hR₁⟩ :=
    omb_absorb_left M Ψ x₀ x hx εx hεx hlimx U (hUopen.mem_nhds hxU)
  obtain ⟨R₂, hR₂⟩ :=
    omb_absorb_left M Ψ x₀ y hy εy hεy hlimy V (hVopen.mem_nhds hyV)
  have hu1 : min R₁ R₂ - 1 < R₁ := by
    calc min R₁ R₂ - 1 < min R₁ R₂ := by linarith
      _ ≤ R₁ := min_le_left _ _
  have hu2 : min R₁ R₂ - 1 < R₂ := by
    calc min R₁ R₂ - 1 < min R₁ R₂ := by linarith
      _ ≤ R₂ := min_le_right _ _
  have huU := hR₁ _ hu1
  have huV := hR₂ _ hu2
  exact (Set.disjoint_left.mp hdisj) huU huV

/-- A cluster point of the `atBot` tail is not a right end. -/
private theorem omb_mapClusterPt_atBot_not_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (m : M) (hmB : (𝓡∂ 1).IsBoundaryPoint m)
    (hm : MapClusterPt m Filter.atBot (ombValPsi M Ψ))
    (hTop : Filter.Tendsto (ombTheta M Ψ x₀ m) (𝓝[>] 0) Filter.atTop) :
    False := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M m hmB
  rcases omb_theta_deriv_sign M Ψ x₀ m ε hε with hpos | hneg
  · exact omb_end_not_both M Ψ x₀ m
      (omb_theta_tendsto_atBot M Ψ x₀ m hmB ε hε hpos) hTop
  · set δ := ε / 2 with hδdef
    have hδpos : 0 < δ := by linarith [hε.1]
    have hδε : δ ≤ ε := by linarith [hε.1]
    have hNopen : IsOpen ((ombHalfCurve M m) '' Set.Ico 0 δ) :=
      omb_halfCurve_image_open M m ε δ hε hδε
    have hNm : m ∈ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      refine ⟨0, ⟨le_refl _, hδpos⟩, ?_⟩
      exact omb_halfCurve_zero M m hmB
    have hfreq : ∃ᶠ u in Filter.atBot,
        ombValPsi M Ψ u ∈ (ombHalfCurve M m) '' Set.Ico 0 δ :=
      mapClusterPt_iff_frequently.mp hm _ (hNopen.mem_nhds hNm)
    have hanti : StrictAntiOn (ombTheta M Ψ x₀ m) (Set.Ioo 0 ε) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioo 0 ε)
        (omb_theta_contDiffOn M Ψ x₀ m ε hε).continuousOn
      rw [interior_Ioo]
      exact hneg
    have hbound : ∀ᶠ u in Filter.atBot,
        ombValPsi M Ψ u ∉ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      filter_upwards [Filter.eventually_le_atBot (ombTheta M Ψ x₀ m δ)]
        with u hu hNu
      obtain ⟨t, htIco, htu⟩ := hNu
      have ht0 : 0 < t := by
        rcases eq_or_lt_of_le htIco.1 with h0 | hpos
        · exfalso
          have htm : ombHalfCurve M m t = m := by
            rw [← h0]
            exact omb_halfCurve_zero M m hmB
          have hfm : m ∈ (ombInterior M : Set M) := by
            rw [← htm, htu]
            exact (Ψ u).2
          exact omb_boundary_not_mem_interior M m hmB (SetLike.mem_coe.mp hfm)
        · exact hpos
      have htIoo : t ∈ Set.Ioo (0 : ℝ) ε :=
        ⟨ht0, lt_of_lt_of_le htIco.2 hδε⟩
      have hδIoo : δ ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
      have hlt : ombTheta M Ψ x₀ m δ < ombTheta M Ψ x₀ m t :=
        hanti htIoo hδIoo htIco.2
      have htu2 : ombValPsi M Ψ (ombTheta M Ψ x₀ m t) = ombHalfCurve M m t :=
        omb_theta_apply M Ψ x₀ m ε hε t htIoo
      have huv : u = ombTheta M Ψ x₀ m t :=
        omb_valPsi_injective M Ψ (htu.symm.trans htu2.symm)
      linarith
    obtain ⟨u, hu1, hu2⟩ := (hfreq.and_eventually hbound).exists
    exact hu2 hu1

/-- A cluster point of the `atTop` tail is not a left end. -/
private theorem omb_mapClusterPt_atTop_not_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (m : M) (hmB : (𝓡∂ 1).IsBoundaryPoint m)
    (hm : MapClusterPt m Filter.atTop (ombValPsi M Ψ))
    (hBot : Filter.Tendsto (ombTheta M Ψ x₀ m) (𝓝[>] 0) Filter.atBot) :
    False := by
  obtain ⟨ε, hε⟩ := omb_exists_halfCurve_radius M m hmB
  rcases omb_theta_deriv_sign M Ψ x₀ m ε hε with hpos | hneg
  · set δ := ε / 2 with hδdef
    have hδpos : 0 < δ := by linarith [hε.1]
    have hδε : δ ≤ ε := by linarith [hε.1]
    have hNopen : IsOpen ((ombHalfCurve M m) '' Set.Ico 0 δ) :=
      omb_halfCurve_image_open M m ε δ hε hδε
    have hNm : m ∈ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      refine ⟨0, ⟨le_refl _, hδpos⟩, ?_⟩
      exact omb_halfCurve_zero M m hmB
    have hfreq : ∃ᶠ u in Filter.atTop,
        ombValPsi M Ψ u ∈ (ombHalfCurve M m) '' Set.Ico 0 δ :=
      mapClusterPt_iff_frequently.mp hm _ (hNopen.mem_nhds hNm)
    have hmono : StrictMonoOn (ombTheta M Ψ x₀ m) (Set.Ioo 0 ε) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioo 0 ε)
        (omb_theta_contDiffOn M Ψ x₀ m ε hε).continuousOn
      rw [interior_Ioo]
      exact hpos
    have hbound : ∀ᶠ u in Filter.atTop,
        ombValPsi M Ψ u ∉ (ombHalfCurve M m) '' Set.Ico 0 δ := by
      filter_upwards [Filter.eventually_ge_atTop (ombTheta M Ψ x₀ m δ)]
        with u hu hNu
      obtain ⟨t, htIco, htu⟩ := hNu
      have ht0 : 0 < t := by
        rcases eq_or_lt_of_le htIco.1 with h0 | hpos
        · exfalso
          have htm : ombHalfCurve M m t = m := by
            rw [← h0]
            exact omb_halfCurve_zero M m hmB
          have hfm : m ∈ (ombInterior M : Set M) := by
            rw [← htm, htu]
            exact (Ψ u).2
          exact omb_boundary_not_mem_interior M m hmB (SetLike.mem_coe.mp hfm)
        · exact hpos
      have htIoo : t ∈ Set.Ioo (0 : ℝ) ε :=
        ⟨ht0, lt_of_lt_of_le htIco.2 hδε⟩
      have hδIoo : δ ∈ Set.Ioo (0 : ℝ) ε := ⟨hδpos, by linarith [hε.1]⟩
      have hlt : ombTheta M Ψ x₀ m t < ombTheta M Ψ x₀ m δ :=
        hmono htIoo hδIoo htIco.2
      have htu2 : ombValPsi M Ψ (ombTheta M Ψ x₀ m t) = ombHalfCurve M m t :=
        omb_theta_apply M Ψ x₀ m ε hε t htIoo
      have huv : u = ombTheta M Ψ x₀ m t :=
        omb_valPsi_injective M Ψ (htu.symm.trans htu2.symm)
      linarith
    obtain ⟨u, hu1, hu2⟩ := (hfreq.and_eventually hbound).exists
    exact hu2 hu1
  · exact omb_end_not_both M Ψ x₀ m hBot
      (omb_theta_tendsto_atTop M Ψ x₀ m hmB ε hε hneg)

/-- One-sided blend of `θ` into the line `α + β·t`, via `smoothTransition`. -/
private def ombBlend (θ : ℝ → ℝ) (α β a : ℝ) : ℝ → ℝ :=
  fun t => (1 - Real.smoothTransition ((t - a) / a)) * θ t +
    Real.smoothTransition ((t - a) / a) * (α + β * t)

/-- Two right ends coincide. -/
private theorem omb_end_unique_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (x y : M)
    (hx : (𝓡∂ 1).IsBoundaryPoint x) (hy : (𝓡∂ 1).IsBoundaryPoint y)
    (hlimx : Filter.Tendsto (ombTheta M Ψ x₀ x) (𝓝[>] 0) Filter.atTop)
    (hlimy : Filter.Tendsto (ombTheta M Ψ x₀ y) (𝓝[>] 0) Filter.atTop) :
    x = y := by
  by_contra hne
  obtain ⟨U, V, hUopen, hVopen, hxU, hyV, hdisj⟩ := t2_separation hne
  obtain ⟨εx, hεx⟩ := omb_exists_halfCurve_radius M x hx
  obtain ⟨εy, hεy⟩ := omb_exists_halfCurve_radius M y hy
  obtain ⟨R₁, hR₁⟩ :=
    omb_absorb_right M Ψ x₀ x hx εx hεx hlimx U (hUopen.mem_nhds hxU)
  obtain ⟨R₂, hR₂⟩ :=
    omb_absorb_right M Ψ x₀ y hy εy hεy hlimy V (hVopen.mem_nhds hyV)
  have hu1 : max R₁ R₂ + 1 > R₁ := by
    calc R₁ ≤ max R₁ R₂ := le_max_left _ _
      _ < max R₁ R₂ + 1 := by linarith
  have hu2 : max R₁ R₂ + 1 > R₂ := by
    calc R₂ ≤ max R₁ R₂ := le_max_right _ _
      _ < max R₁ R₂ + 1 := by linarith
  have huU := hR₁ _ hu1
  have huV := hR₂ _ hu2
  exact (Set.disjoint_left.mp hdisj) huU huV

/-- There is a left end: a cluster point of the `atBot` tail. -/
private theorem omb_exists_left_end (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) :
    ∃ q : M, (𝓡∂ 1).IsBoundaryPoint q ∧
      Filter.Tendsto (ombTheta M Ψ x₀ q) (𝓝[>] 0) Filter.atBot := by
  have hleBot : Filter.map (ombValPsi M Ψ) Filter.atBot ≤ Filter.principal (Set.univ : Set M) := by
    simp
  obtain ⟨m, _, hm⟩ := isCompact_univ.exists_mapClusterPt hleBot
  have hmB : (𝓡∂ 1).IsBoundaryPoint m := by
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) m
      with hI | hB
    · exfalso
      exact omb_mapClusterPt_atBot_not_mem M Ψ m hm
        (SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M m).mpr hI))
    · exact hB
  rcases omb_theta_tendsto M Ψ x₀ m hmB with hL | hR
  · exact ⟨m, hmB, hL⟩
  · exfalso
    exact omb_mapClusterPt_atBot_not_right M Ψ x₀ m hmB hm hR

/-- There is a right end: a cluster point of the `atTop` tail. -/
private theorem omb_exists_right_end (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) :
    ∃ p : M, (𝓡∂ 1).IsBoundaryPoint p ∧
      Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  have hleTop : Filter.map (ombValPsi M Ψ) Filter.atTop ≤ Filter.principal (Set.univ : Set M) := by
    simp
  obtain ⟨m, _, hm⟩ := isCompact_univ.exists_mapClusterPt hleTop
  have hmB : (𝓡∂ 1).IsBoundaryPoint m := by
    rcases ModelWithCorners.isInteriorPoint_or_isBoundaryPoint (I := 𝓡∂ 1) m
      with hI | hB
    · exfalso
      exact omb_mapClusterPt_atTop_not_mem M Ψ m hm
        (SetLike.mem_coe.mpr ((omb_mem_ombInterior_iff M m).mpr hI))
    · exact hB
  rcases omb_theta_tendsto M Ψ x₀ m hmB with hL | hR
  · exfalso
    exact omb_mapClusterPt_atTop_not_left M Ψ x₀ m hmB hm hL
  · exact ⟨m, hmB, hR⟩

/-- The boundary is exactly one left end and one right end. -/
private theorem omb_boundary_eq_pair (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) :
    ∃ q p : M, q ≠ p ∧ ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p} ∧
      Filter.Tendsto (ombTheta M Ψ x₀ q) (𝓝[>] 0) Filter.atBot ∧
      Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop := by
  obtain ⟨q, hqb, hqlim⟩ := omb_exists_left_end M Ψ x₀
  obtain ⟨p, hpb, hplim⟩ := omb_exists_right_end M Ψ x₀
  have hne : q ≠ p := by
    intro hcon
    rw [hcon] at hqlim
    exact omb_end_not_both M Ψ x₀ p hqlim hplim
  refine ⟨q, p, hne, ?_, hqlim, hplim⟩
  ext z
  constructor
  · intro hz
    have hzb : (𝓡∂ 1).IsBoundaryPoint z := hz
    rcases omb_theta_tendsto M Ψ x₀ z hzb with hL | hR
    · left
      exact omb_end_unique_left M Ψ x₀ z q hzb hqb hL hqlim
    · right
      exact omb_end_unique_right M Ψ x₀ z p hzb hpb hR hplim
  · intro hz
    rcases Set.mem_insert_iff.mp hz with h | h
    · rw [h]
      exact hqb
    · rw [Set.mem_singleton_iff.mp h]
      exact hpb

/-- Sign extraction: a left end has positive derivative on the tail. -/
private theorem omb_theta_sign_of_atBot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atBot) :
    ∀ t ∈ Set.Ioo 0 ε, 0 < deriv (ombTheta M Ψ x₀ p) t := by
  rcases omb_theta_deriv_sign M Ψ x₀ p ε hε with hpos | hneg
  · exact hpos
  · exfalso
    exact omb_end_not_both M Ψ x₀ p hlim
      (omb_theta_tendsto_atTop M Ψ x₀ p hp ε hε hneg)

/-- Sign extraction: a right end has negative derivative on the tail. -/
private theorem omb_theta_sign_of_atTop (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M] [T2Space M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (p : M) (hp : (𝓡∂ 1).IsBoundaryPoint p)
    (ε : ℝ) (hε : ombGoodRadius M p ε)
    (hlim : Filter.Tendsto (ombTheta M Ψ x₀ p) (𝓝[>] 0) Filter.atTop) :
    ∀ t ∈ Set.Ioo 0 ε, deriv (ombTheta M Ψ x₀ p) t < 0 := by
  rcases omb_theta_deriv_sign M Ψ x₀ p ε hε with hpos | hneg
  · exfalso
    exact omb_end_not_both M Ψ x₀ p
      (omb_theta_tendsto_atBot M Ψ x₀ p hp ε hε hpos) hlim
  · exact hneg

/-- Gluing setup: ends, radii, and the interpolating reparametrisation. -/
private theorem omb_glue_setup (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    ∃ (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M)) (x₀ : ↥(ombInterior M))
      (q p : M) (εq εp a : ℝ) (φ : ℝ → ℝ),
      (𝓡∂ 1).IsBoundaryPoint q ∧ (𝓡∂ 1).IsBoundaryPoint p ∧ q ≠ p ∧
      ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p} ∧
      ombGoodRadius M q εq ∧ ombGoodRadius M p εp ∧
      0 < a ∧ a < 1 / 2 ∧ a ≤ εq ∧ a ≤ εp ∧
      ContDiffOn ℝ ∞ φ (Set.Ioo 0 1) ∧
      (∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t) ∧ φ '' Set.Ioo 0 1 = Set.univ ∧
      Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a) ∧
      Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1) := by
  obtain ⟨Ψ⟩ := omb_exists_diffeomorph_real_interior M hB
  obtain ⟨xw, hxw⟩ := omb_nonempty_ombInterior M
  refine ⟨Ψ, ⟨xw, hxw⟩, ?_⟩
  obtain ⟨q, p, hne, hbp_eq, hqlim, hplim⟩ := omb_boundary_eq_pair M Ψ ⟨xw, hxw⟩
  have hqb : (𝓡∂ 1).IsBoundaryPoint q := by
    change q ∈ ModelWithCorners.boundary (I := 𝓡∂ 1) M
    rw [hbp_eq]
    exact Set.mem_insert q {p}
  have hpb : (𝓡∂ 1).IsBoundaryPoint p := by
    change p ∈ ModelWithCorners.boundary (I := 𝓡∂ 1) M
    rw [hbp_eq]
    exact Set.mem_insert_of_mem q rfl
  obtain ⟨εq, hεq⟩ := omb_exists_halfCurve_radius M q hqb
  obtain ⟨εp, hεp⟩ := omb_exists_halfCurve_radius M p hpb
  have hposq := omb_theta_sign_of_atBot M Ψ ⟨xw, hxw⟩ q hqb εq hεq hqlim
  have hnegp := omb_theta_sign_of_atTop M Ψ ⟨xw, hxw⟩ p hpb εp hεp hplim
  have hb0 : 0 < min (min εq εp) (1 / 2) :=
    lt_min (lt_min hεq.1 hεp.1) (by norm_num)
  have hb12 : min (min εq εp) (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hbεq : min (min εq εp) (1 / 2) ≤ εq :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hbεp : min (min εq εp) (1 / 2) ≤ εp :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hθq : ContDiffOn ℝ ∞ (ombTheta M Ψ ⟨xw, hxw⟩ q)
      (Set.Ioo 0 (min (min εq εp) (1 / 2))) :=
    (omb_theta_contDiffOn M Ψ ⟨xw, hxw⟩ q εq hεq).mono
      (Set.Ioo_subset_Ioo le_rfl hbεq)
  have hθp : ContDiffOn ℝ ∞ (ombTheta M Ψ ⟨xw, hxw⟩ p)
      (Set.Ioo 0 (min (min εq εp) (1 / 2))) :=
    (omb_theta_contDiffOn M Ψ ⟨xw, hxw⟩ p εp hεp).mono
      (Set.Ioo_subset_Ioo le_rfl hbεp)
  have hposq' : ∀ t ∈ Set.Ioo 0 (min (min εq εp) (1 / 2)),
      0 < deriv (ombTheta M Ψ ⟨xw, hxw⟩ q) t :=
    fun t ht => hposq t (Set.Ioo_subset_Ioo le_rfl hbεq ht)
  have hnegp' : ∀ t ∈ Set.Ioo 0 (min (min εq εp) (1 / 2)),
      deriv (ombTheta M Ψ ⟨xw, hxw⟩ p) t < 0 :=
    fun t ht => hnegp t (Set.Ioo_subset_Ioo le_rfl hbεp ht)
  obtain ⟨a, ha, hab, φ, hφD, hφderiv, hφsurj, eleft, eright⟩ :=
    omb_exists_interpolation (ombTheta M Ψ ⟨xw, hxw⟩ q)
      (ombTheta M Ψ ⟨xw, hxw⟩ p) _ hb0 hb12 hθq hθp hposq' hnegp' hqlim hplim
  have hbp_eq : ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p} := by
    ext z
    constructor
    · intro hz
      have hzb : (𝓡∂ 1).IsBoundaryPoint z := hz
      rcases omb_theta_tendsto M Ψ ⟨xw, hxw⟩ z hzb with hL | hR
      · left
        exact omb_end_unique_left M Ψ ⟨xw, hxw⟩ z q hzb hqb hL hqlim
      · right
        exact omb_end_unique_right M Ψ ⟨xw, hxw⟩ z p hzb hpb hR hplim
    · intro hz
      rcases Set.mem_insert_iff.mp hz with h | h
      · rw [h]
        exact hqb
      · rw [Set.mem_singleton_iff.mp h]
        exact hpb
  refine ⟨q, p, εq, εp, a, φ, hqb, hpb, hne, hbp_eq, hεq, hεp, ha, ?_, ?_, ?_,
    hφD, hφderiv, hφsurj, eleft, eright⟩
  · exact lt_of_lt_of_le hab hb12
  · exact le_trans (le_of_lt hab) hbεq
  · exact le_trans (le_of_lt hab) hbεp

/-- The gluing map `Set.Icc 0 1 → M`: left half-curve, right half-curve, middle. -/
private def ombGlueF (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ) : Set.Icc (0 : ℝ) 1 → M := by
  classical
  exact fun z =>
    if z.val < a then ombHalfCurve M q z.val
    else if 1 - a < z.val then ombHalfCurve M p (1 - z.val)
    else ombValPsi M Ψ (φ z.val)

/-- The gluing map is a local diffeomorphism on the left piece. -/
private theorem ombGlueF_local_left (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq : ℝ) (hεq : ombGoodRadius M q εq)
    (haεq : a ≤ εq) (ha12 : a < 1 / 2)
    (z : Set.Icc (0 : ℝ) 1) (hz : z.val < a) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) z := by
  have hz1 : z.val < 1 := lt_trans hz (lt_trans ha12 (by norm_num))
  have hsrc : z ∈ (IccLeftChart 0 1).source := by
    change z.val < 1
    exact hz1
  have htgt : IccLeftChart 0 1 z ∈ (chartAt (EuclideanHalfSpace 1) q).target := by
    rw [← omb_symm_leftChart z]
    apply hεq.2.2
    have h0 : 0 ≤ z.val := z.property.1
    rw [abs_of_nonneg h0]
    exact lt_of_lt_of_le hz haεq
  have hchart := omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas
    (IccLeftChart 0 1) omb_IccLeftChart_mem_maximalAtlas
    (chartAt (EuclideanHalfSpace 1) q)
    (IsManifold.chart_mem_maximalAtlas q) z hsrc htgt
  have hU : IsOpen {w : Set.Icc (0 : ℝ) 1 | w.val < a} := by
    have e : {w : Set.Icc (0 : ℝ) 1 | w.val < a} = Subtype.val ⁻¹' Set.Iio a :=
      rfl
    rw [e]
    exact isOpen_Iio.preimage continuous_subtype_val
  have hev : ombGlueF M Ψ q p a φ =ᶠ[𝓝 z]
      ((chartAt (EuclideanHalfSpace 1) q).symm ∘ IccLeftChart 0 1) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (ombGlueF_of_lt M Ψ q p a φ w hw).trans
      (omb_halfCurve_leftChart M q w)
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hchart hev

/-- The gluing map is a local diffeomorphism on the right piece. -/
private theorem ombGlueF_local_right (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εp : ℝ) (hεp : ombGoodRadius M p εp)
    (haεp : a ≤ εp) (ha12 : a < 1 / 2)
    (z : Set.Icc (0 : ℝ) 1) (hright : 1 - a < z.val) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) z := by
  have h0z : 0 < z.val := lt_trans (by linarith : (0 : ℝ) < 1 - a) hright
  have hsrc : z ∈ (IccRightChart 0 1).source := by
    change 0 < z.val
    exact h0z
  have htgt : IccRightChart 0 1 z ∈ (chartAt (EuclideanHalfSpace 1) p).target := by
    rw [← omb_symm_rightChart z]
    apply hεp.2.2
    have hle : 0 ≤ 1 - z.val := by linarith [z.property.2]
    rw [abs_of_nonneg hle]
    calc 1 - z.val < a := by linarith
      _ ≤ εp := haεp
  have hchart := omb_isLocalDiffeomorphAt_symm_comp_of_mem_maximalAtlas
    (IccRightChart 0 1) omb_IccRightChart_mem_maximalAtlas
    (chartAt (EuclideanHalfSpace 1) p)
    (IsManifold.chart_mem_maximalAtlas p) z hsrc htgt
  have hU : IsOpen {w : Set.Icc (0 : ℝ) 1 | 1 - a < w.val} := by
    have e : {w : Set.Icc (0 : ℝ) 1 | 1 - a < w.val} =
        Subtype.val ⁻¹' Set.Ioi (1 - a) := rfl
    rw [e]
    exact isOpen_Ioi.preimage continuous_subtype_val
  have hev : ombGlueF M Ψ q p a φ =ᶠ[𝓝 z]
      ((chartAt (EuclideanHalfSpace 1) p).symm ∘ IccRightChart 0 1) := by
    filter_upwards [hU.mem_nhds hright] with w hw
    have hwleft : ¬ w.val < a := by
      have : 1 - a < w.val := hw
      linarith [ha12]
    exact (ombGlueF_of_gt M Ψ q p a φ w hwleft hw).trans
      (omb_halfCurve_rightChart M p w)
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hchart hev

/-- On the open interval, the gluing map is the middle composite. -/
private theorem ombGlueF_eq_mid (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z : Set.Icc (0 : ℝ) 1) (h0 : 0 < z.val) (h1 : z.val < 1) :
    ombGlueF M Ψ q p a φ z = ombValPsi M Ψ (φ z.val) := by
  by_cases hleft : z.val < a
  · rw [ombGlueF_of_lt M Ψ q p a φ z hleft]
    have hmem : z.val ∈ Set.Ioo (0 : ℝ) a := ⟨h0, hleft⟩
    have eφ : φ z.val = ombTheta M Ψ x₀ q z.val := eleft hmem
    rw [eφ]
    have hε : z.val ∈ Set.Ioo (0 : ℝ) εq := ⟨h0, lt_of_lt_of_le hleft haεq⟩
    exact (omb_theta_apply M Ψ x₀ q εq hεq z.val hε).symm
  · by_cases hright : 1 - a < z.val
    · rw [ombGlueF_of_gt M Ψ q p a φ z hleft hright]
      have hmem : z.val ∈ Set.Ioo (1 - a) 1 := ⟨hright, h1⟩
      have eφ : φ z.val = ombTheta M Ψ x₀ p (1 - z.val) := eright hmem
      rw [eφ]
      have h1w : (1 - z.val) ∈ Set.Ioo (0 : ℝ) εp :=
        ⟨by linarith, lt_of_lt_of_le (by linarith) haεp⟩
      exact (omb_theta_apply M Ψ x₀ p εp hεp (1 - z.val) h1w).symm
    · exact ombGlueF_of_mid M Ψ q p a φ z hleft hright

/-- The gluing map is a local diffeomorphism on the middle piece. -/
private theorem ombGlueF_local_mid (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z : Set.Icc (0 : ℝ) 1) (h0 : 0 < z.val) (h1 : z.val < 1) :
    IsLocalDiffeomorphAt (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) z := by
  obtain ⟨Φ, hΦsrc, hΦfun, -, -, -⟩ :=
    odm_exists_partialDiffeomorph_of_deriv_pos (Set.Ioo 0 1) φ isOpen_Ioo
      (isPreconnected_iff_ordConnected.mp isPreconnected_Ioo) hφD hφderiv
  have h1φ : IsLocalDiffeomorphAt (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ Subtype.val z :=
    omb_isLocalDiffeomorphAt_Icc_val z h0 h1
  have hmem : z.val ∈ Φ.source := by
    rw [hΦsrc]
    exact ⟨h0, h1⟩
  have h2φ0 := PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Φ hmem
  rw [hΦfun] at h2φ0
  have h3φ : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ ⇑Ψ (φ z.val) :=
    Ψ.isLocalDiffeomorph _
  have h4φ : IsLocalDiffeomorphAt (𝓡 1) (𝓡∂ 1) ∞ Subtype.val (Ψ (φ z.val)) :=
    omb_isLocalDiffeomorph_val M x₀ _
  have h12 := IsLocalDiffeomorphAt.comp (K := 𝓘(ℝ, ℝ)) (P := ℝ) h1φ h2φ0
  have h123 := IsLocalDiffeomorphAt.comp (K := 𝓡 1) (P := ↥(ombInterior M)) h12 h3φ
  have hcomp := IsLocalDiffeomorphAt.comp (K := (𝓡∂ 1)) (P := M) h123 h4φ
  have hU : IsOpen {w : Set.Icc (0 : ℝ) 1 | 0 < w.val ∧ w.val < 1} := by
    have e : {w : Set.Icc (0 : ℝ) 1 | 0 < w.val ∧ w.val < 1} =
        Subtype.val ⁻¹' Set.Ioo (0 : ℝ) 1 := rfl
    rw [e]
    exact isOpen_Ioo.preimage continuous_subtype_val
  have hev : ombGlueF M Ψ q p a φ =ᶠ[𝓝 z]
      (Subtype.val ∘ ⇑Ψ ∘ φ ∘ Subtype.val) := by
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with w hw
    exact ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft eright
      w hw.1 hw.2
  exact odm_isLocalDiffeomorphAt_congr_of_eventuallyEq hcomp hev

/-- The gluing map is a local diffeomorphism everywhere. -/
private theorem ombGlueF_isLocalDiffeomorph (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1)) :
    IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞ (ombGlueF M Ψ q p a φ) := by
  intro z
  by_cases hleft : z.val < a
  · exact ombGlueF_local_left M Ψ q p a φ εq hεq haεq ha12 z hleft
  · by_cases hright : 1 - a < z.val
    · exact ombGlueF_local_right M Ψ q p a φ εp hεp haεp ha12 z hright
    · have h0 : 0 < z.val := lt_of_lt_of_le ha0 (le_of_not_gt hleft)
      have h1 : z.val < 1 :=
        lt_of_le_of_lt (le_of_not_gt hright) (by linarith)
      exact ombGlueF_local_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp hφD
        hφderiv eleft eright z h0 h1

/-- The gluing map sends `⊥` to the left end. -/
private theorem ombGlueF_bot (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (hqb : (𝓡∂ 1).IsBoundaryPoint q) :
    ombGlueF M Ψ q p a φ ⊥ = q := by
  have h0a : (⊥ : Set.Icc (0 : ℝ) 1).val < a := by
    rw [Set.Icc.coe_bot]
    exact ha0
  rw [ombGlueF_of_lt M Ψ q p a φ ⊥ h0a, Set.Icc.coe_bot]
  exact omb_halfCurve_zero M q hqb

/-- The gluing map sends `⊤` to the right end. -/
private theorem ombGlueF_top (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (hpb : (𝓡∂ 1).IsBoundaryPoint p) :
    ombGlueF M Ψ q p a φ ⊤ = p := by
  have hna : ¬ (⊤ : Set.Icc (0 : ℝ) 1).val < a := by
    rw [Set.Icc.coe_top]
    have hle : a ≤ 1 := by linarith
    exact not_lt.mpr hle
  have hgt : 1 - a < (⊤ : Set.Icc (0 : ℝ) 1).val := by
    rw [Set.Icc.coe_top]
    linarith
  rw [ombGlueF_of_gt M Ψ q p a φ ⊤ hna hgt, Set.Icc.coe_top]
  have e0 : (1 : ℝ) - (1 : ℝ) = 0 := by norm_num
  rw [e0]
  exact omb_halfCurve_zero M p hpb

/-- The gluing map sends a point of value `0` to the left end. -/
private theorem ombGlueF_of_val_zero (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (hqb : (𝓡∂ 1).IsBoundaryPoint q)
    (z : Set.Icc (0 : ℝ) 1) (hz0 : z.val = 0) :
    ombGlueF M Ψ q p a φ z = q := by
  have h0a : z.val < a := by
    rw [hz0]
    exact ha0
  rw [ombGlueF_of_lt M Ψ q p a φ z h0a, hz0]
  exact omb_halfCurve_zero M q hqb

/-- The gluing map sends a point of value `1` to the right end. -/
private theorem ombGlueF_of_val_one (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (hpb : (𝓡∂ 1).IsBoundaryPoint p)
    (z : Set.Icc (0 : ℝ) 1) (hz1 : z.val = 1) :
    ombGlueF M Ψ q p a φ z = p := by
  have hna : ¬ z.val < a := by
    rw [hz1]
    have hle : a ≤ 1 := by linarith
    exact not_lt.mpr hle
  have hgt : 1 - a < z.val := by
    rw [hz1]
    linarith
  rw [ombGlueF_of_gt M Ψ q p a φ z hna hgt]
  have e0 : (1 : ℝ) - z.val = 0 := by
    rw [hz1]
    norm_num
  rw [e0]
  exact omb_halfCurve_zero M p hpb

/-- Interior points of `Icc` land in the interior of `M`. -/
private theorem ombGlueF_mem_interior (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z : Set.Icc (0 : ℝ) 1) (h0 : 0 < z.val) (h1 : z.val < 1) :
    ombGlueF M Ψ q p a φ z ∈ (ombInterior M : Set M) := by
  rw [ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft eright z h0
    h1]
  exact (Ψ (φ z.val)).2

/-- The gluing map is injective on interior points of `Icc`. -/
private theorem ombGlueF_interior_inj (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1))
    (z₁ z₂ : Set.Icc (0 : ℝ) 1)
    (h10 : 0 < z₁.val) (h11 : z₁.val < 1) (h20 : 0 < z₂.val) (h21 : z₂.val < 1)
    (h12 : ombGlueF M Ψ q p a φ z₁ = ombGlueF M Ψ q p a φ z₂) :
    z₁ = z₂ := by
  have hmono : StrictMonoOn φ (Set.Ioo 0 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1) hφD.continuousOn
    rw [interior_Ioo]
    exact hφderiv
  have e1 := ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft
    eright z₁ h10 h11
  have e2 := ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft
    eright z₂ h20 h21
  rw [e1, e2] at h12
  have hcomp : Function.Injective (Subtype.val ∘ ⇑Ψ) :=
    Subtype.val_injective.comp Ψ.toEquiv.injective
  have e : (Subtype.val ∘ ⇑Ψ) = ombValPsi M Ψ := rfl
  rw [e] at hcomp
  have hφ : φ z₁.val = φ z₂.val := hcomp h12
  have hval : z₁.val = z₂.val := hmono.injOn ⟨h10, h11⟩ ⟨h20, h21⟩ hφ
  exact Subtype.ext hval

/-- The gluing map is injective. -/
private theorem ombGlueF_injective (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (hne : q ≠ p)
    (hqb : (𝓡∂ 1).IsBoundaryPoint q) (hpb : (𝓡∂ 1).IsBoundaryPoint p)
    (ha0 : 0 < a) (ha12 : a < 1 / 2) (haεq : a ≤ εq) (haεp : a ≤ εp)
    (hφD : ContDiffOn ℝ ∞ φ (Set.Ioo 0 1))
    (hφderiv : ∀ t ∈ Set.Ioo 0 1, 0 < deriv φ t)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1)) :
    Function.Injective (ombGlueF M Ψ q p a φ) := by
  have hqS : q ∉ (ombInterior M : Set M) := omb_boundary_not_mem_interior M q hqb
  have hpS : p ∉ (ombInterior M : Set M) := omb_boundary_not_mem_interior M p hpb
  have hpos_of_ne_zero : ∀ z : Set.Icc (0 : ℝ) 1, z.val ≠ 0 → 0 < z.val := by
    intro z hz
    exact lt_of_le_of_ne' z.property.1 hz
  intro z₁ z₂ h12
  by_cases hz1bot : z₁.val = 0
  · have e1 : z₁ = ⊥ :=
      Subtype.ext (by rw [Set.Icc.coe_bot]; exact hz1bot)
    have e2 : z₂ = ⊥ := by
      by_cases hz2bot : z₂.val = 0
      · exact Subtype.ext (by rw [Set.Icc.coe_bot]; exact hz2bot)
      · exfalso
        have hpos := hpos_of_ne_zero z₂ hz2bot
        have hFq : ombGlueF M Ψ q p a φ z₂ = q := by
          rw [← h12, e1]
          exact ombGlueF_bot M Ψ q p a φ ha0 hqb
        by_cases hz2top : z₂.val = 1
        · have hFp : ombGlueF M Ψ q p a φ z₂ = p :=
            ombGlueF_of_val_one M Ψ q p a φ ha0 ha12 hpb z₂ hz2top
          exact hne (hFq.symm.trans hFp)
        · have hlt : z₂.val < 1 := lt_of_le_of_ne z₂.property.2 hz2top
          have hS := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
            haεp eleft eright z₂ hpos hlt
          rw [hFq] at hS
          exact hqS hS
    exact e1.trans e2.symm
  · by_cases hz1top : z₁.val = 1
    · have e1 : z₁ = ⊤ :=
        Subtype.ext (by rw [Set.Icc.coe_top]; exact hz1top)
      have hFp2 : ombGlueF M Ψ q p a φ z₂ = p := by
        rw [← h12, e1]
        exact ombGlueF_top M Ψ q p a φ ha0 ha12 hpb
      by_cases hz2bot : z₂.val = 0
      · exfalso
        have hFq : ombGlueF M Ψ q p a φ z₂ = q :=
          ombGlueF_of_val_zero M Ψ q p a φ ha0 hqb z₂ hz2bot
        exact hne (hFq.symm.trans hFp2)
      · have hpos := hpos_of_ne_zero z₂ hz2bot
        by_cases hz2top : z₂.val = 1
        · exact e1.trans
              (Subtype.ext (by rw [Set.Icc.coe_top]; exact hz2top)).symm
        · exfalso
          have hlt : z₂.val < 1 := lt_of_le_of_ne z₂.property.2 hz2top
          have hS := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
            haεp eleft eright z₂ hpos hlt
          rw [hFp2] at hS
          exact hpS hS
    · have h10 : 0 < z₁.val := hpos_of_ne_zero z₁ hz1bot
      have h11 : z₁.val < 1 := lt_of_le_of_ne z₁.property.2 hz1top
      by_cases hz2bot : z₂.val = 0
      · exfalso
        have hS1 := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
          haεp eleft eright z₁ h10 h11
        rw [h12] at hS1
        have hFq : ombGlueF M Ψ q p a φ z₂ = q :=
          ombGlueF_of_val_zero M Ψ q p a φ ha0 hqb z₂ hz2bot
        rw [hFq] at hS1
        exact hqS hS1
      · have hpos := hpos_of_ne_zero z₂ hz2bot
        by_cases hz2top : z₂.val = 1
        · exfalso
          have hS1 := ombGlueF_mem_interior M Ψ x₀ q p a φ εq εp hεq hεp haεq
            haεp eleft eright z₁ h10 h11
          rw [h12] at hS1
          have hFp : ombGlueF M Ψ q p a φ z₂ = p :=
            ombGlueF_of_val_one M Ψ q p a φ ha0 ha12 hpb z₂ hz2top
          rw [hFp] at hS1
          exact hpS hS1
        · have h21 : z₂.val < 1 := lt_of_le_of_ne z₂.property.2 hz2top
          exact ombGlueF_interior_inj M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp
            hφD hφderiv eleft eright z₁ z₂ h10 h11 hpos h21 h12

/-- The gluing map is surjective. -/
private theorem ombGlueF_surjective (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    (Ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓡 1⟯ ↥(ombInterior M))
    (x₀ : ↥(ombInterior M)) (q p : M) (a : ℝ) (φ : ℝ → ℝ)
    (εq εp : ℝ) (hεq : ombGoodRadius M q εq) (hεp : ombGoodRadius M p εp)
    (haεq : a ≤ εq) (haεp : a ≤ εp)
    (ha0 : 0 < a) (ha12 : a < 1 / 2)
    (hqb : (𝓡∂ 1).IsBoundaryPoint q) (hpb : (𝓡∂ 1).IsBoundaryPoint p)
    (hbp_eq : ModelWithCorners.boundary (I := 𝓡∂ 1) M = {q, p})
    (hφsurj : φ '' Set.Ioo 0 1 = Set.univ)
    (eleft : Set.EqOn φ (ombTheta M Ψ x₀ q) (Set.Ioo 0 a))
    (eright : Set.EqOn φ (fun t => ombTheta M Ψ x₀ p (1 - t)) (Set.Ioo (1 - a) 1)) :
    Function.Surjective (ombGlueF M Ψ q p a φ) := by
  intro m
  have hunion : m ∈ (↑(ombInterior M) : Set M) ∪ {q, p} := by
    have h := ModelWithCorners.interior_union_boundary_eq_univ (I := 𝓡∂ 1) (M := M)
    rw [hbp_eq] at h
    change m ∈ (𝓡∂ 1).interior M ∪ {q, p}
    rw [h]
    exact Set.mem_univ m
  rcases hunion with hmS | hmqp
  · obtain ⟨u₀, hu₀⟩ := omb_mem_interior_eq_valPsi M Ψ m hmS
    have hmem : u₀ ∈ φ '' Set.Ioo 0 1 := by
      rw [hφsurj]
      exact Set.mem_univ u₀
    obtain ⟨t, ht, htu⟩ := hmem
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    refine ⟨⟨t, htIcc⟩, ?_⟩
    have h0 : (0 : ℝ) < (⟨t, htIcc⟩ : Set.Icc (0 : ℝ) 1).val := ht.1
    have h1 : (⟨t, htIcc⟩ : Set.Icc (0 : ℝ) 1).val < 1 := ht.2
    rw [ombGlueF_eq_mid M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp eleft eright _
      h0 h1]
    rw [htu]
    exact hu₀
  · rcases Set.mem_insert_iff.mp hmqp with h | h
    · rw [h]
      exact ⟨⊥, ombGlueF_bot M Ψ q p a φ ha0 hqb⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨⊤, ombGlueF_top M Ψ q p a φ ha0 ha12 hpb⟩

/-- Boundary case: `M` is diffeomorphic to `Set.Icc 0 1`. -/
private theorem omb_diffeomorph_Icc_of_boundary_nonempty (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M]
    (hB : (ModelWithCorners.boundary (I := 𝓡∂ 1) M).Nonempty) :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨Ψ, x₀, q, p, εq, εp, a, φ, hqb, hpb, hne, hbp_eq, hεq, hεp, ha0,
    ha12, haεq, haεp, hφD, hφderiv, hφsurj, eleft, eright⟩ := omb_glue_setup M hB
  have hld := ombGlueF_isLocalDiffeomorph M Ψ x₀ q p a φ εq εp hεq hεp ha0
    ha12 haεq haεp hφD hφderiv eleft eright
  have hinj := ombGlueF_injective M Ψ x₀ q p a φ εq εp hεq hεp hne hqb hpb ha0
    ha12 haεq haεp hφD hφderiv eleft eright
  have hsurj := ombGlueF_surjective M Ψ x₀ q p a φ εq εp hεq hεp haεq haεp ha0
    ha12 hqb hpb hbp_eq hφsurj eleft eright
  exact ⟨(hld.diffeomorphOfBijective ⟨hinj, hsurj⟩).symm⟩

/--
Every compact connected Hausdorff second-countable smooth 1-manifold with boundary (`𝓡∂ 1`) is
diffeomorphic to either `Circle` or `Icc (0:ℝ) 1`. Source: Classification of 1-manifolds with
boundary; Hirsch, Differential Topology; J. Lee, Introduction to Smooth Manifolds, 2nd ed.,
collar theorem; Lean states compact connected `𝓡∂ 1` with closed interval specialization.

Proves `Wanted` entry `compact_connected_one_manifold_with_boundary_classification`.
-/
theorem compact_connected_one_manifold_with_boundary_classification
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
    [IsManifold (𝓡∂ 1) ∞ M]
    [T2Space M] [CompactSpace M] [ConnectedSpace M] [SecondCountableTopology M] :
    Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡 1⟯ Circle) ∨ Nonempty (M ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ (Set.Icc (0 : ℝ) 1)) := by
  rcases Set.eq_empty_or_nonempty (ModelWithCorners.boundary (I := 𝓡∂ 1) M) with
    hB | hB
  · exact Or.inl (omb_circle_of_boundary_empty M hB)
  · obtain ⟨D⟩ := omb_diffeomorph_Icc_of_boundary_nonempty M hB
    exact Or.inr ⟨D⟩

end MathlibExt.Geometry.Manifold.OneDimensionalWanted
