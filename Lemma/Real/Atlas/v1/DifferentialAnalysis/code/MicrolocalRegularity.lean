import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.MicrolocalRegularity.Part2
open WavefrontSet
open scoped SchwartzMap


namespace WavefrontSet

/--
[schwEmbed_toSchwartzOfEmptyCss](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
lemma schwEmbed_toSchwartzOfEmptyCss
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (h : Css u = ∅) :
-- imply
  ConeSupport.schwEmbed (toSchwartzOfEmptyCss u h) = u :=
-- proof
  ((ConeSupport.coneSingularSupport_eq_empty_iff u).mp
    (coneSingularSupport_empty_of_Css_empty u h)).choose_spec

end WavefrontSet

namespace WavefrontSet

/--
[smul_partition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
lemma smul_partition
  {n : ℕ}
  {n : ℕ}
  {φ : EuclideanSpace ℝ (Fin n) → ℂ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hφ : φ.HasTemperateGrowth) :
-- imply
  TemperedDistribution.smulLeftCLM ℂ φ u + TemperedDistribution.smulLeftCLM ℂ (1 - φ) u = u := by
-- proof
  have h1 : (1 : EuclideanSpace ℝ (Fin n) → ℂ).HasTemperateGrowth :=
    Function.HasTemperateGrowth.const 1
  have h1φ : (1 - φ).HasTemperateGrowth := h1.sub hφ
  have hadd := TemperedDistribution.smulLeftCLM_add (F := ℂ) hφ h1φ
  have hone : φ + (1 - φ) = (1 : EuclideanSpace ℝ (Fin n) → ℂ) := by
    ext x; simp [Pi.add_apply, Pi.sub_apply]
  rw [hone] at hadd
  have key := congr_arg (· u) hadd.symm
  simp only [ContinuousLinearMap.add_apply] at key
  rw [key]
  have h_one_eq : (1 : EuclideanSpace ℝ (Fin n) → ℂ) = fun _ => (1 : ℂ) := rfl
  rw [h_one_eq, TemperedDistribution.smulLeftCLM_const, one_smul]

end WavefrontSet

namespace WavefrontSet

/--
[schwEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
lemma schwEmbed_injective
  {n : ℕ}
  {n : ℕ}
  {f g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ}
-- given
  (h : ConeSupport.schwEmbed f = ConeSupport.schwEmbed g) :
-- imply
  f = g := by
-- proof
  open MeasureTheory in
  rw [← sub_eq_zero]
  have hfg : ConeSupport.schwEmbed (f - g) = 0 := by
    simp only [map_sub, h, sub_self]
  apply SchwartzMap.injective_toLp (F := ℂ) (E := EuclideanSpace ℝ (Fin n)) 2 (μ := volume)
  have hLp_eq : Lp.toTemperedDistribution ((f - g).toLp 2 volume) =
    (0 : TemperedDistribution (EuclideanSpace ℝ (Fin n)) ℂ) := by
    rwa [Lp.toTemperedDistribution_toLp_eq]
  have hinj := Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (E := EuclideanSpace ℝ (Fin n)) (μ := volume) (p := 2)
  rw [LinearMap.ker_eq_bot'] at hinj
  exact hinj _ hLp_eq

end WavefrontSet

namespace WavefrontSet

/--
[css_empty_of_conicSupport_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
lemma css_empty_of_conicSupport_disjoint
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {K : Set (ClosedBall n)}
-- given
  (hχ : χ.HasTemperateGrowth)
  (hK : Css u ⊆ K)
  (hdisjoint : ∀ ω : ConeSupport.Sphere n, ω ∈ ConeSupport.ConicSingularSupportSphere u → ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℂ) (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → ψ (a • x) = ψ x) (R : ℝ) (_ : 0 < R), (∀ x, R < ‖x‖ → χ x = ψ x) ∧ ψ (↑ω) = 0) :
-- imply
  Css (TemperedDistribution.smulLeftCLM ℂ χ u) = ∅ := by
-- proof
  by_cases hne : Set.Nonempty (ConeSupport.ConicSingularSupportSphere u)
  ·
    obtain ⟨ω₀, hω₀⟩ := hne
    obtain ⟨ψ₀, hψ₀_hom, R₀, hR₀, hχ_eq₀, hψ₀_zero⟩ := hdisjoint ω₀ hω₀
    have hψ₀_disjoint : ∀ ω : ConeSupport.Sphere n,
      ω ∈ ConeSupport.ConicSingularSupportSphere u → ψ₀ (↑ω) = 0 := by
      intro ω₁ hω₁
      obtain ⟨ψ₁, hψ₁_hom, R₁, hR₁, hχ_eq₁, hψ₁_zero⟩ := hdisjoint ω₁ hω₁
      have hψ_agree : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ψ₀ x = ψ₁ x := by
        intro x hx
        set a := (max R₀ R₁ + 1) / ‖x‖ with ha_def
        have hx_norm_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
        have ha_pos : (0 : ℝ) < a := by
          apply div_pos
          · linarith [le_max_left R₀ R₁]
          · exact hx_norm_pos
        have hax_norm : ‖a • x‖ = a * ‖x‖ := by
          rw [norm_smul, Real.norm_of_nonneg ha_pos.le]
        have hax_gt_R₀ : R₀ < ‖a • x‖ := by
          rw [hax_norm, ha_def, div_mul_cancel₀]
          · linarith [le_max_left R₀ R₁]
          · exact ne_of_gt hx_norm_pos
        have hax_gt_R₁ : R₁ < ‖a • x‖ := by
          rw [hax_norm, ha_def, div_mul_cancel₀]
          · linarith [le_max_right R₀ R₁]
          · exact ne_of_gt hx_norm_pos
        calc ψ₀ x = ψ₀ (a • x) := (hψ₀_hom a ha_pos x hx).symm
          _ = χ (a • x) := (hχ_eq₀ (a • x) hax_gt_R₀).symm
          _ = ψ₁ (a • x) := hχ_eq₁ (a • x) hax_gt_R₁
          _ = ψ₁ x := hψ₁_hom a ha_pos x hx
      have hω₁_ne : (↑ω₁ : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
        intro h_eq
        have := ω₁.property
        rw [Metric.mem_sphere, dist_zero_right] at this
        rw [h_eq, norm_zero] at this
        linarith
      rwa [hψ_agree (↑ω₁) hω₁_ne]
    have hχ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      exact_mod_cast hχ.1
    obtain ⟨f, hf⟩ := ConeSupport.css_disjoint_implies_schwartz_general u χ hχ_smooth
      R₀ hR₀ ψ₀ hψ₀_hom hχ_eq₀ hψ₀_disjoint
    rw [hf]
    have h_cone : ConeSupport.coneSingularSupport (ConeSupport.schwEmbed f) = ∅ :=
      (ConeSupport.coneSingularSupport_eq_empty_iff _).mpr ⟨f, rfl⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Css, Set.mem_setOf_eq] at hp
    simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff,
      Set.image_eq_empty] at h_cone
    obtain ⟨h_ss, h_csss⟩ := h_cone
    split_ifs at hp with hh
    · rw [Set.eq_empty_iff_forall_notMem] at h_csss
      exact h_csss _ hp
    · rw [Set.eq_empty_iff_forall_notMem] at h_ss
      exact h_ss _ hp
  ·
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hχ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      exact_mod_cast hχ.1
    have hcss_decomp := ConeSupport.hasEmptyConicSingularSupportSphere_of_eq_empty u hne
    obtain ⟨⟨f₀, g, hg_compact, hsum⟩⟩ := hcss_decomp.hasDecomp
    have hχ_u_eq : TemperedDistribution.smulLeftCLM ℂ χ u =
      TemperedDistribution.smulLeftCLM ℂ χ (ConeSupport.schwEmbed f₀) +
      TemperedDistribution.smulLeftCLM ℂ χ g := by
      rw [hsum, map_add]
    have hχf₀ : TemperedDistribution.smulLeftCLM ℂ χ (ConeSupport.schwEmbed f₀) =
      (ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f₀)) :=
      ConeSupport.smulLeftCLM_schwartz_embed hχ f₀
    obtain ⟨K_g, hK_g_compact, hK_g_supp⟩ := hg_compact
    obtain ⟨R_g, hR_g⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK_g_compact.isBounded
    let R_g' := max R_g 0
    have hR_g'_pos : 0 < R_g' + 1 := by positivity
    let bump_g : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
      { rIn := R_g' + 1, rOut := R_g' + 2, rIn_pos := hR_g'_pos, rIn_lt_rOut := by linarith }
    let θ : EuclideanSpace ℝ (Fin n) → ℂ := Complex.ofRealCLM ∘ bump_g
    have hθ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ :=
      Complex.ofRealCLM.contDiff.comp bump_g.contDiff
    have hθ_compact : HasCompactSupport θ :=
      bump_g.hasCompactSupport.comp_left (map_zero _)
    have hθ_tg : Function.HasTemperateGrowth θ := hθ_compact.hasTemperateGrowth hθ_smooth
    obtain ⟨f_g', hf_g'⟩ := ConeSupport.smulLeftCLM_schwartz_of_compactSmooth g θ
      hθ_smooth hθ_compact hθ_tg
    have hθg_eq_g : TemperedDistribution.smulLeftCLM ℂ θ g = g := by
      apply ConeSupport.smulLeftCLM_eq_self_of_one_on_support g K_g hK_g_compact hK_g_supp θ
        hθ_smooth hθ_compact
      · intro x hx
        simp only [θ, Function.comp, Complex.ofRealCLM_apply]
        have hx_in : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) bump_g.rIn := by
          apply Metric.closedBall_subset_closedBall (show R_g ≤ R_g' + 1 by
            exact le_add_of_le_of_nonneg (le_max_left R_g 0) one_pos.le)
          exact hR_g hx
        rw [bump_g.one_of_mem_closedBall hx_in]
        simp [Complex.ofReal_one]
      · exact hθ_tg
    have hg_schwartz : g = ConeSupport.schwEmbed f_g' := by
      rw [← hθg_eq_g, hf_g']
    have hχg_eq : TemperedDistribution.smulLeftCLM ℂ χ g =
      ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f_g') := by
      rw [hg_schwartz]
      exact ConeSupport.smulLeftCLM_schwartz_embed hχ f_g'
    set f_g := SchwartzMap.smulLeftCLM ℂ χ f_g'
    have hf_g : TemperedDistribution.smulLeftCLM ℂ χ g = ConeSupport.schwEmbed f_g := hχg_eq
    have hχ_u_schwartz : TemperedDistribution.smulLeftCLM ℂ χ u =
      ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f₀ + f_g) := by
      rw [hχ_u_eq, hχf₀, hf_g, map_add]
    rw [hχ_u_schwartz]
    have h_cone : ConeSupport.coneSingularSupport
      (ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f₀ + f_g)) = ∅ :=
      (ConeSupport.coneSingularSupport_eq_empty_iff _).mpr
        ⟨SchwartzMap.smulLeftCLM ℂ χ f₀ + f_g, rfl⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Css, Set.mem_setOf_eq] at hp
    simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff,
      Set.image_eq_empty] at h_cone
    obtain ⟨h_ss, h_csss⟩ := h_cone
    split_ifs at hp with hh
    · rw [Set.eq_empty_iff_forall_notMem] at h_csss
      exact h_csss _ hp
    · rw [Set.eq_empty_iff_forall_notMem] at h_ss
      exact h_ss _ hp

end WavefrontSet

namespace WavefrontSet

/--
[smulLeft_complement_eq_zero_of_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
lemma smulLeft_complement_eq_zero_of_fixed
  {n : ℕ}
  {n : ℕ}
  {χ : EuclideanSpace ℝ (Fin n) → ℂ}
  {v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hχ : χ.HasTemperateGrowth)
  (hfix : TemperedDistribution.smulLeftCLM ℂ χ v = v) :
-- imply
  TemperedDistribution.smulLeftCLM ℂ (1 - χ) v = 0 := by
-- proof
  have hpart := smul_partition χ hχ v
  have : TemperedDistribution.smulLeftCLM ℂ χ v +
    TemperedDistribution.smulLeftCLM ℂ (1 - χ) v = v := hpart
  rw [hfix] at this
  have := sub_eq_zero.mpr this
  simp only [add_sub_cancel_left] at this
  exact this
/-- Existence of auxiliary Schwartz representatives `c₁, c₂` such that pairings of `u₁` and `u₂`
with the Schwartz preimages of the cutoff differences factor through the embeddings of `c₁` and
`c₂`, and the cross-pairings agree. -/

end WavefrontSet

/--
[ConicSingularSupportSphere_empty_of_Css_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
private lemma ConicSingularSupportSphere_empty_of_Css_empty_eq
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (h : Css u = ∅) :
-- imply
  ConeSupport.ConicSingularSupportSphere u = ∅ := by
-- proof
  apply WavefrontSet.ConicSingularSupportSphere_empty_of_Css_empty u h

/--
[singularSupport_empty_of_Css_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
private lemma singularSupport_empty_of_Css_empty_eq
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (h : Css u = ∅) :
-- imply
  ConeSupport.singularSupport u = ∅ := by
-- proof
  apply WavefrontSet.singularSupport_empty_of_Css_empty u h

/--
[coneSingularSupport_empty_of_Css_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean)
-/
@[path]
private lemma coneSingularSupport_empty_of_Css_empty_eq
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (h : Css u = ∅) :
-- imply
  ConeSupport.coneSingularSupport u = ∅ := by
-- proof
  apply WavefrontSet.coneSingularSupport_empty_of_Css_empty u h


-- created on 2026-10-23
