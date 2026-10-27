import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
open Set AffineWeylGroupFullData
open scoped InnerProductSpace


/--
[affineHyperplane_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
private lemma affineHyperplane_ext
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {h₀ h₁ : AffineHyperplane E}
-- given
  (hn : h₀.normal = h₁.normal)
  (ho : h₀.offset = h₁.offset) :
-- imply
  h₀ = h₁ := by
-- proof
  cases h₀
  cases h₁
  simp_all

/--
[affineWeylGroup_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylProposition12_5.lean)
-/
@[path]
private lemma affineWeylGroup_locallyFinite
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  d.affineArr.IsLocallyFinite := by
-- proof
  intro x
  refine ⟨1, one_pos, ?_⟩
  have hS_fin : Set.Finite (⋃ α ∈ d.roots,
    ⋃ k ∈ {k : ℤ | |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1},
      ({⟨α, ↑k, d.roots_ne_zero α ‹_›⟩} : Set (AffineHyperplane E))) := by
    apply Set.Finite.biUnion' d.roots_finite
    intro α hα
    apply Set.Finite.biUnion
    ·
      apply Set.Finite.subset (Set.finite_Icc
        (⌊⟪α, x⟫_ℝ - (‖α‖ + 1)⌋)
        (⌈⟪α, x⟫_ℝ + (‖α‖ + 1)⌉))
      intro k hk
      simp only [Set.mem_ofPred_eq] at hk
      simp only [Set.mem_Icc]
      have hk_abs := abs_sub_lt_iff.mp hk
      exact ⟨Int.floor_le_iff.mpr (by push_cast; linarith [hk_abs.2]),
        Int.le_ceil_iff.mpr (by push_cast; linarith [hk_abs.1])⟩
    ·
      intro _ _
      exact Set.finite_singleton _
  apply hS_fin.subset
  intro η ⟨hη_arr, hη_meet⟩
  obtain ⟨y, hy_ball, hy_carrier⟩ := hη_meet
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη_arr
  simp only [AffineHyperplane.carrier, Set.mem_ofPred_eq] at hy_carrier
  rw [Metric.mem_ball] at hy_ball
  have h_cs : |⟪α, y - x⟫_ℝ| ≤ ‖α‖ * ‖y - x‖ := abs_real_inner_le_norm α (y - x)
  have h_dist : ‖y - x‖ < 1 := by rwa [← dist_eq_norm]
  have h_bound : |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1 := by
    have h1 : ⟪η.normal, y⟫_ℝ = η.offset := hy_carrier
    rw [hα_eq] at h1
    have heq : |↑k - ⟪α, x⟫_ℝ| = |⟪α, y - x⟫_ℝ| := by
      have : ↑k = ⟪α, y⟫_ℝ := by linarith [h1, hk_eq]
      rw [this, ← inner_sub_right]
    calc |↑k - ⟪α, x⟫_ℝ|
        = |⟪α, y - x⟫_ℝ| := heq
      _ ≤ ‖α‖ * ‖y - x‖ := h_cs
      _ < ‖α‖ * 1 := by
        obtain h0 | h0 := eq_or_lt_of_le (norm_nonneg α)
        ·
          exact absurd (norm_eq_zero.mp h0.symm) (d.roots_ne_zero α hα)
        ·
          exact mul_lt_mul_of_pos_left h_dist h0
      _ ≤ ‖α‖ + 1 := by linarith [norm_nonneg α]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨α, hα, k, h_bound, affineHyperplane_ext hα_eq (by rw [hk_eq])⟩

/--
[coroot_translation_eq_composition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylProposition12_5.lean)
-/
@[path]
private lemma coroot_translation_eq_composition
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v) := by
-- proof
  intro v
  set c := d.coroot α
  have hc : ⟪α, c⟫_ℝ = 2 := by
    simp only [c]
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact inner_self_ne_zero.mpr (d.roots_ne_zero α hα)
  simp only [affineReflFun, Int.cast_zero, Int.cast_one, sub_zero]
  have hw : ⟪α, v - ⟪α, v⟫_ℝ • c⟫_ℝ = -⟪α, v⟫_ℝ := by
    simp [inner_sub_right, inner_smul_right, hc]
    ring
  rw [hw]
  module


-- created on 2026-10-23
-- updated on 2026-10-26
