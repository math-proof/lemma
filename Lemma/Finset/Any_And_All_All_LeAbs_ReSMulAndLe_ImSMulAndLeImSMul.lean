import Mathlib
import sympy.Basic

open scoped UpperHalfPlane MatrixGroups

/--
[ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularGroup_exists_bounds_smul_of_mem_fd_of_im_le.lean)
-/
@[main]
private lemma main
  {S : Finset SL(2, ℤ)}
  {Y : ℝ} :
-- imply
  ∃ B y₀ Y₁ : ℝ, 0 < y₀ ∧ ∀ σ ∈ S, ∀ z ∈ ModularGroup.fd, z.im ≤ Y →
      |(σ • z).re| ≤ B ∧ y₀ ≤ (σ • z).im ∧ (σ • z).im ≤ Y₁ := by
-- proof
  set K : Set ℍ := ⋃ σ ∈ S, (fun z : ℍ => σ • z) '' ModularGroup.truncatedFundamentalDomain Y
  have hK : IsCompact K := S.isCompact_biUnion fun σ _ =>
    (ModularGroup.isCompact_truncatedFundamentalDomain Y).image (by
      change Continuous fun z : ℍ => ((σ : SL(2, ℝ)) • z)
      exact continuous_const_smul _)
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuous_abs.comp UpperHalfPlane.continuous_re).continuousOn
  obtain ⟨Y₁, hY₁⟩ := hK.bddAbove_image UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨y₀, hy₀, hlow⟩ : ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ w ∈ K, y₀ ≤ w.im := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨x, -, hmin⟩ := hK.exists_isMinOn hKne UpperHalfPlane.continuous_im.continuousOn
      exact ⟨x.im, x.im_pos, fun w hw => hmin hw⟩
  refine ⟨B, y₀, Y₁, hy₀, fun σ hσ z hz hzY => ?_⟩
  have hw : σ • z ∈ K := Set.mem_iUnion₂.mpr ⟨σ, hσ, z, ⟨hz, hzY⟩, rfl⟩
  exact ⟨hB ⟨_, hw, rfl⟩, hlow _ hw, hY₁ ⟨_, hw, rfl⟩⟩


-- created on 2026-10-05
