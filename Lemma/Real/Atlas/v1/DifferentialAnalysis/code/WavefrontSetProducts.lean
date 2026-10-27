import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.WavefrontSetProducts
open MeasureTheory WavefrontSet
open scoped SchwartzMap FourierTransform


namespace WavefrontSet

/--
[not_mem_css_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma not_mem_css_zero
  {n : ℕ}
  {p : ClosedBall n} :
-- imply
  p ∉ Css (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by
-- proof
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, 0, by simp [map_zero]⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_, 0, by simp [map_zero]⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
      b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_fourier_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma not_mem_css_fourier_zero
  {n : ℕ}
  {q : ClosedBall n} :
-- imply
  q ∉ Css (𝓕 (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))) := by
-- proof
  have h0 : 𝓕 (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) = 0 := by ext g; simp
  rw [h0]
  exact not_mem_css_zero q
set_option maxHeartbeats 400000 in

end WavefrontSet

namespace WavefrontSet

/--
[css_subadditive_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma css_subadditive_not_mem
  {n : ℕ}
  {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p : ClosedBall n}
-- given
  (h₁ : p ∉ Css u₁)
  (h₂ : p ∉ Css u₂) :
-- imply
  p ∉ Css (u₁ + u₂) := by
-- proof
  simp only [Css, Set.mem_setOf] at h₁ h₂ ⊢
  split_ifs with h
  ·
    rw [dif_pos h] at h₁ h₂
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    obtain ⟨g₁, hg₁_conic, f₁, hf₁⟩ := h₁
    obtain ⟨g₂, hg₂_conic, f₂, hf₂⟩ := h₂
    refine ⟨g₁ * g₂, ?_, ?_⟩
    ·
      obtain ⟨hg₁_smooth, R₁, hR₁, hR₁_lt, R₀₁, hR₀₁, hg₁_supp, ψ₁, hψ₁_hom, hψ₁_ne, hg₁_eq⟩ := hg₁_conic
      obtain ⟨hg₂_smooth, R₂, hR₂, hR₂_lt, R₀₂, hR₀₂, hg₂_supp, ψ₂, hψ₂_hom, hψ₂_ne, hg₂_eq⟩ := hg₂_conic
      refine ⟨hg₁_smooth.mul hg₂_smooth, max R₁ R₂, lt_max_of_lt_left hR₁,
        max_lt hR₁_lt hR₂_lt,
        max R₀₁ R₀₂, lt_max_of_lt_left hR₀₁, ?_, ψ₁ * ψ₂, ?_, ?_, ?_⟩
      ·
        intro x hx
        simp only [Set.mem_setOf]
        rw [Function.mem_support, Pi.mul_apply] at hx
        have hx_ne : g₁ x ≠ 0 ∧ g₂ x ≠ 0 := mul_ne_zero_iff.mp hx
        have h1 : x ∈ Function.support g₁ := Function.mem_support.mpr hx_ne.1
        have h2 : x ∈ Function.support g₂ := Function.mem_support.mpr hx_ne.2
        exact max_le (hg₁_supp h1) (hg₂_supp h2)
      ·
        intro a ha x hx
        simp only [Pi.mul_apply]
        rw [hψ₁_hom a ha x hx, hψ₂_hom a ha x hx]
      ·
        simp only [Pi.mul_apply]
        exact mul_ne_zero hψ₁_ne hψ₂_ne
      ·
        intro x hx
        simp only [Pi.mul_apply]
        rw [hg₁_eq x (lt_of_le_of_lt (le_max_left _ _) hx),
          hg₂_eq x (lt_of_le_of_lt (le_max_right _ _) hx)]
    ·
      have hg₁_tg : Function.HasTemperateGrowth g₁ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₁ _ hg₁_conic
      have hg₂_tg : Function.HasTemperateGrowth g₂ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₂ _ hg₂_conic
      have eq1 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ =
        TemperedDistribution.smulLeftCLM ℂ g₂ (TemperedDistribution.smulLeftCLM ℂ g₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₁_tg hg₂_tg u₁).symm
      have mul_comm_g : g₂ * g₁ = g₁ * g₂ := mul_comm g₂ g₁
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ =
        TemperedDistribution.smulLeftCLM ℂ g₁ (TemperedDistribution.smulLeftCLM ℂ g₂ u₂) := by
        rw [← mul_comm_g]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₂_tg hg₁_tg u₂).symm
      rw [show TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) (u₁ + u₂) =
        TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ +
        TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ from
        map_add (TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂)) u₁ u₂]
      rw [eq1, hf₁, eq2, hf₂]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₂_tg f₁]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ g₂ f₁ + SchwartzMap.smulLeftCLM ℂ g₁ f₂,
        (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩
  ·
    rw [dif_neg h] at h₁ h₂
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    obtain ⟨φ₁, hφ₁_smooth, hφ₁_supp, hφ₁_ne, f₁, hf₁⟩ := h₁
    obtain ⟨φ₂, hφ₂_smooth, hφ₂_supp, hφ₂_ne, f₂, hf₂⟩ := h₂
    have hφ₁_tg : Function.HasTemperateGrowth φ₁ := hφ₁_supp.hasTemperateGrowth hφ₁_smooth
    have hφ₂_tg : Function.HasTemperateGrowth φ₂ := hφ₂_supp.hasTemperateGrowth hφ₂_smooth
    refine ⟨φ₁ * φ₂, hφ₁_smooth.mul hφ₂_smooth, hφ₁_supp.mul_right, ?_, ?_⟩
    ·
      simp only [Pi.mul_apply]
      exact mul_ne_zero hφ₁_ne hφ₂_ne
    ·
      have eq1 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₁ =
        TemperedDistribution.smulLeftCLM ℂ φ₂ (TemperedDistribution.smulLeftCLM ℂ φ₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₁_tg hφ₂_tg u₁).symm
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₂ =
        TemperedDistribution.smulLeftCLM ℂ φ₁ (TemperedDistribution.smulLeftCLM ℂ φ₂ u₂) := by
        rw [← mul_comm φ₂ φ₁]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₂_tg hφ₁_tg u₂).symm
      rw [ConeSupport.smulLeftCLM_add_right]
      rw [eq1, hf₁, eq2, hf₂]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₂_tg f₁]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ φ₂ f₁ + SchwartzMap.smulLeftCLM ℂ φ₁ f₂,
        (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_implies_not_mem_wfsc_fst'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma not_mem_css_implies_not_mem_wfsc_fst'
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (hp : p ∉ Css u)
  (hpq : (p, q) ∈ BoundaryProd n) :
-- imply
  (p, q) ∉ WFsc u := by
-- proof
  rw [not_mem_wfsc_iff_exists_decomp hpq]
  exact ⟨u, 0, (add_zero u).symm, hp, not_mem_css_fourier_zero q⟩

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_css_fourier_implies_not_mem_wfsc_snd'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma not_mem_css_fourier_implies_not_mem_wfsc_snd'
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (hq : q ∉ Css (𝓕 u))
  (hpq : (p, q) ∈ BoundaryProd n) :
-- imply
  (p, q) ∉ WFsc u := by
-- proof
  rw [not_mem_wfsc_iff_exists_decomp hpq]
  exact ⟨0, u, (zero_add u).symm, not_mem_css_zero p, hq⟩

end WavefrontSet

namespace WavefrontSet

/--
[wfsc_subadditive'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma wfsc_subadditive'
  {n : ℕ}
  {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (h₁ : (p, q) ∉ WFsc u₁)
  (h₂ : (p, q) ∉ WFsc u₂) :
-- imply
  (p, q) ∉ WFsc (u₁ + u₂) := by
-- proof
  by_cases hpq : (p, q) ∈ BoundaryProd n
  ·
    rw [not_mem_wfsc_iff_exists_decomp hpq] at h₁ h₂ ⊢
    obtain ⟨a₁, b₁, hu₁, hp_a₁, hq_fb₁⟩ := h₁
    obtain ⟨a₂, b₂, hu₂, hp_a₂, hq_fb₂⟩ := h₂
    refine ⟨a₁ + a₂, b₁ + b₂, ?_, ?_, ?_⟩
    ·
      rw [hu₁, hu₂]; abel
    ·
      exact css_subadditive_not_mem hp_a₁ hp_a₂
    ·
      rw [FourierTransform.fourier_add]
      exact css_subadditive_not_mem hq_fb₁ hq_fb₂
  ·
    simp only [BoundaryProd, Set.mem_setOf_eq, not_or] at hpq
    obtain ⟨hp_ne, hq_ne⟩ := hpq
    simp only [WFsc, Set.mem_setOf_eq, not_not]
    rw [dif_neg hp_ne]
    simp only [WFsc, Set.mem_setOf_eq, not_not] at h₁
    rw [dif_neg hp_ne] at h₁
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, hq_css⟩ := h₁
    refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
    rw [ConeSupport.smulLeftCLM_add_right, FourierTransform.fourier_add]
    apply css_subadditive_not_mem hq_css
    simp only [Css, Set.mem_setOf, dif_neg hq_ne, ConeSupport.singularSupport, not_not]
    obtain ⟨f, hf⟩ :=
      ConeSupport.fourier_smulLeftCLM_eq_schwartzConvolution φ hφ_smooth hφ_compact u₂
    rw [hf]
    exact ConeSupport.isSmoothNear_schwartzConvolution (𝓕 u₂) f _

end WavefrontSet

namespace WavefrontSet

/--
[exists_decomp_of_not_mem_wfsc'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma exists_decomp_of_not_mem_wfsc'
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (hpq : (p, q) ∈ BoundaryProd n)
  (h : (p, q) ∉ WFsc u) :
-- imply
  ∃ u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), u = u₁ + u₂ ∧ p ∉ Css u₁ ∧ q ∉ Css (𝓕 u₂) :=
-- proof
  (not_mem_wfsc_iff_exists_decomp hpq).mp h

end WavefrontSet

namespace WavefrontSet

/--
[not_mem_wfsc_iff_exists_css_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontSetProducts.lean)
-/
@[path]
lemma not_mem_wfsc_iff_exists_css_decomp
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {p q : ClosedBall n}
-- given
  (hpq : (p, q) ∈ BoundaryProd n) :
-- imply
  (p, q) ∉ WFsc u ↔ ∃ u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), u = u₁ + u₂ ∧ p ∉ Css u₁ ∧ q ∉ Css (𝓕 u₂) := by
-- proof
  constructor
  · exact exists_decomp_of_not_mem_wfsc' hpq
  · rintro ⟨u₁, u₂, hudecomp, hp_u₁, hq_fu₂⟩
    have h₁ : (p, q) ∉ WFsc u₁ :=
      not_mem_css_implies_not_mem_wfsc_fst' u₁ p q hp_u₁ hpq
    have h₂ : (p, q) ∉ WFsc u₂ :=
      not_mem_css_fourier_implies_not_mem_wfsc_snd' u₂ p q hq_fu₂ hpq
    rw [hudecomp]
    exact wfsc_subadditive' u₁ u₂ p q h₁ h₂
end WavefrontSet



-- created on 2026-10-23
