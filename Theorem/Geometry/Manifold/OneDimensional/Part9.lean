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
import Def.Geometry.Manifold.OneDimensional.Part7
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

/-- A left end absorbs far-left values into any of its neighbourhoods. -/
theorem omb_absorb_left (M : Type*) [TopologicalSpace M]
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
theorem omb_absorb_right (M : Type*) [TopologicalSpace M]
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
theorem omb_theta_tendsto (M : Type*) [TopologicalSpace M]
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
theorem omb_end_unique_left (M : Type*) [TopologicalSpace M]
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
theorem omb_mapClusterPt_atBot_not_right (M : Type*) [TopologicalSpace M]
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
theorem omb_mapClusterPt_atTop_not_left (M : Type*) [TopologicalSpace M]
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

end MathlibExt.Geometry.Manifold.OneDimensionalWanted
end
