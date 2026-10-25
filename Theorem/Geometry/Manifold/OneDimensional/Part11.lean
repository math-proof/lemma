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
import Def.Geometry.Manifold.OneDimensional.Part9
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

/-- The gluing map is a local diffeomorphism on the left piece. -/
theorem ombGlueF_local_left (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_local_right (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_eq_mid (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_local_mid (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_isLocalDiffeomorph (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_bot (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_top (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_of_val_zero (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_of_val_one (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_mem_interior (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_interior_inj (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_injective (M : Type*) [TopologicalSpace M]
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
theorem ombGlueF_surjective (M : Type*) [TopologicalSpace M]
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
theorem omb_diffeomorph_Icc_of_boundary_nonempty (M : Type*) [TopologicalSpace M]
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
end
