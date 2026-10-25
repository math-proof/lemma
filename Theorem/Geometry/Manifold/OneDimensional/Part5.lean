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
import Def.Geometry.Manifold.OneDimensional.Part4
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
/-- The half-chart curve maps the open interval into the target box. -/
theorem omb_halfCurve_maps_fwd (p : M) (ε : ℝ)
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
theorem omb_halfCurve_left_inv (p : M) (ε : ℝ)
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
theorem omb_halfCurve_right_inv (p : M) (ε : ℝ)
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
theorem omb_halfCurveInv_maps (p : M) (ε : ℝ) :
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
theorem omb_halfCurve_contMDiffOn (p : M) (ε : ℝ)
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
theorem omb_isLocalDiffeomorphAt_halfCurve (p : M) (ε t : ℝ)
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
theorem omb_halfCurve_image_open (p : M) (ε δ : ℝ)
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
theorem omb_nonempty_ombInterior [ConnectedSpace M] :
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
theorem omb_closure_ombInterior [ConnectedSpace M] :
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
theorem omb_tail_side [ConnectedSpace M]
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
theorem omb_cap_inter_subset (p : M)
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

end BoundaryInterior
end MathlibExt.Geometry.Manifold.OneDimensionalClassification
end
