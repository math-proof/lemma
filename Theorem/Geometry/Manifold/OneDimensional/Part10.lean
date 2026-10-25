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
import Def.Geometry.Manifold.OneDimensional.Part8
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

open scoped Manifold ContDiff

namespace MathlibExt.Geometry.Manifold.OneDimensionalWanted

open MathlibExt.Geometry.Manifold.OneDimensionalClassification

/-- Two right ends coincide. -/
theorem omb_end_unique_right (M : Type*) [TopologicalSpace M]
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
theorem omb_exists_left_end (M : Type*) [TopologicalSpace M]
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
theorem omb_exists_right_end (M : Type*) [TopologicalSpace M]
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
theorem omb_boundary_eq_pair (M : Type*) [TopologicalSpace M]
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
theorem omb_theta_sign_of_atBot (M : Type*) [TopologicalSpace M]
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
theorem omb_theta_sign_of_atTop (M : Type*) [TopologicalSpace M]
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
theorem omb_glue_setup (M : Type*) [TopologicalSpace M]
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

end MathlibExt.Geometry.Manifold.OneDimensionalWanted
end
