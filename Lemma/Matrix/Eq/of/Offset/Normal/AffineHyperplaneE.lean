import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
open Set AffineWeylGroupFullData
open scoped InnerProductSpace


namespace AffineWeylGroupFullData

/--
[affineHyperplane_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma affineHyperplane_ext
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
-- given
  (h0 h1 : AffineHyperplane E)
  (hn : h0.normal = h1.normal)
  (ho : h0.offset = h1.offset) :
-- imply
  h0 = h1 := by
-- proof
  cases h1; cases h2; simp_all

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma locallyFinite
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
    · apply Set.Finite.subset (Set.finite_Icc
      (⌊⟪α, x⟫_ℝ - (‖α‖ + 1)⌋)
      (⌈⟪α, x⟫_ℝ + (‖α‖ + 1)⌉))
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      simp only [Set.mem_Icc]
      have hk_abs := abs_sub_lt_iff.mp hk
      exact ⟨Int.floor_le_iff.mpr (by push_cast; linarith [hk_abs.2]),
        Int.le_ceil_iff.mpr (by push_cast; linarith [hk_abs.1])⟩
    · intro _ _; exact Set.finite_singleton _
  apply hS_fin.subset
  intro η ⟨hη_arr, hη_meet⟩
  obtain ⟨y, hy_ball, hy_carrier⟩ := hη_meet
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη_arr
  simp only [AffineHyperplane.carrier, Set.mem_setOf_eq] at hy_carrier
  rw [Metric.mem_ball] at hy_ball
  have h_cs : |⟪α, y - x⟫_ℝ| ≤ ‖α‖ * ‖y - x‖ := abs_real_inner_le_norm α (y - x)
  have h_dist : ‖y - x‖ < 1 := by rwa [← dist_eq_norm]
  have h_bound : |↑k - ⟪α, x⟫_ℝ| < ‖α‖ + 1 := by
    have h1 : ⟪η.normal, y⟫_ℝ = η.offset := hy_carrier
    rw [hα_eq] at h1
    calc |↑k - ⟪α, x⟫_ℝ|
      = |⟪α, y⟫_ℝ - ⟪α, x⟫_ℝ| := by congr 1; linarith [h1, hk_eq]
      _ = |⟪α, y - x⟫_ℝ| := by rw [inner_sub_right]
      _ ≤ ‖α‖ * ‖y - x‖ := h_cs
      _ < ‖α‖ * 1 := by
        obtain h0 | h0 := eq_or_lt_of_le (norm_nonneg α)
        · exact absurd (norm_eq_zero.mp h0.symm) (d.roots_ne_zero α hα)
        · exact mul_lt_mul_of_pos_left h_dist h0
      _ ≤ ‖α‖ + 1 := by linarith [norm_nonneg α]
  simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
  exact ⟨α, hα, k, h_bound, affineHyperplane_ext _ _ hα_eq (by linarith [hk_eq])⟩

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[stable_corootLattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma stable_corootLattice
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  ∀ v ∈ d.corootLattice, ∀ η ∈ d.affineArr.hyperplanes, ∃ η' ∈ d.affineArr.hyperplanes, η'.normal = η.normal ∧ ∀ x : E, x ∈ η'.carrier ↔ (x - v) ∈ η.carrier := by
-- proof
  intro v hv η hη
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη
  obtain ⟨m, hm⟩ := d.corootLattice_int α hα v hv
  refine ⟨⟨α, ↑(k + m), d.roots_ne_zero α hα⟩, ⟨α, hα, k + m, rfl, rfl⟩, ?_, ?_⟩
  · exact hα_eq.symm
  · intro x
    simp only [AffineHyperplane.carrier, Set.mem_setOf_eq]
    rw [hα_eq, hk_eq, inner_sub_right, real_inner_comm v α]
    constructor
    · intro h; push_cast at h; linarith
    · intro h; push_cast; linarith

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[stable_weylGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma stable_weylGroup
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  ∀ w ∈ d.weylGroup, ∀ η ∈ d.affineArr.hyperplanes, ∃ η' ∈ d.affineArr.hyperplanes, η'.normal = (w : E ≃ₗᵢ[ℝ] E) η.normal ∧ η'.offset = η.offset := by
-- proof
  intro w hw η hη
  obtain ⟨α, hα, k, hα_eq, hk_eq⟩ := hη
  refine ⟨⟨(w : E ≃ₗᵢ[ℝ] E) α, ↑k, ?_⟩, ?_, ?_, ?_⟩
  · intro h; exact d.roots_ne_zero α hα ((w : E ≃ₗᵢ[ℝ] E).injective (by simp [h]))
  · exact ⟨(w : E ≃ₗᵢ[ℝ] E) α, d.weylGroup_stable_roots w hw α hα, k, rfl, rfl⟩
  · rw [hα_eq]
  · rw [hk_eq]

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[affineRefl_eq_translation_comp_linearRefl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma affineRefl_eq_translation_comp_linearRefl
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
  {k : ℤ}
  {v : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  d.affineReflFun α k v = d.linearReflFun α v + (k : ℝ) • d.coroot α := by
-- proof
  simp only [affineReflFun, linearReflFun, sub_smul]
  abel

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[translation_coroot_eq_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma translation_coroot_eq_comp
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
  {v : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  v + d.coroot α = d.affineReflFun α 1 (d.linearReflFun α v) := by
-- proof
  simp only [affineReflFun, linearReflFun]
  have h_inner : ⟪α, d.coroot α⟫_ℝ = 2 := by
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact (inner_self_ne_zero.mpr (d.roots_ne_zero α hα))
  simp only [inner_sub_right, inner_smul_right, h_inner]
  push_cast
  module

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[semidirect_product_affineWeylGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma semidirect_product_affineWeylGroup
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  ∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E, ∃ (t : E), t ∈ d.corootLattice ∧ d.affineReflFun α k v = d.linearReflFun α v + t := by
-- proof
  intro α hα k v
  refine ⟨(k : ℝ) • d.coroot α, ?_, ?_⟩
  ·
    have hcr_mem := d.coroot_mem_lattice α hα
    have hzsmul : (k : ℤ) • d.coroot α ∈ d.corootLattice :=
      d.corootLattice.zsmul_mem hcr_mem k
    convert hzsmul using 1
    exact Int.cast_smul_eq_zsmul ℝ k (d.coroot α)
  · exact d.affineRefl_eq_translation_comp_linearRefl α hα k v

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[linear_inter_translation_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma linear_inter_translation_trivial
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {w : E ≃ₗᵢ[ℝ] E}
  {t : E}
-- given
  (h : ∀ v : E, w v = v + t) :
-- imply
  t = 0 ∧ w = 1 := by
-- proof
  have h0 : w 0 = 0 + t := h 0
  have hw0 : w 0 = 0 := map_zero w
  rw [hw0, zero_add] at h0
  constructor
  · exact h0.symm
  · ext v
    have hv := h v
    rw [← h0] at hv
    simp only [LinearIsometryEquiv.coe_one, id_eq]
    simp only [add_zero] at hv
    exact hv

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[weylGroup_normalizes_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma weylGroup_normalizes_lattice
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  ∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice, (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice :=
-- proof
  d.weylGroup_stable_corootLattice

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[reflection_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma reflection_involutive
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {η : AffineHyperplane E} :
-- imply
  η.reflectionMap * η.reflectionMap = 1 := by
-- proof
  ext x
  simp only [AffineIsometryEquiv.coe_mul, Function.comp_apply, AffineIsometryEquiv.coe_one, id_eq]
  exact EuclideanGeometry.reflection_reflection η.toAffineSubspace x

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[linearRefl_eq_affineRefl_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma linearRefl_eq_affineRefl_zero
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
  {v : E} :
-- imply
  d.linearReflFun α v = d.affineReflFun α 0 v := by
-- proof
  simp only [linearReflFun, affineReflFun, Int.cast_zero, sub_zero]

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[affineReflFun_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma affineReflFun_involutive
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
  {k : ℤ}
  {v : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  d.affineReflFun α k (d.affineReflFun α k v) = v := by
-- proof
  simp only [affineReflFun]
  have h_inner : ⟪α, d.coroot α⟫_ℝ = 2 := by
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact (inner_self_ne_zero.mpr (d.roots_ne_zero α hα))
  simp only [inner_sub_right, inner_smul_right, h_inner]
  push_cast
  module

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[affineReflFun_fixed_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma affineReflFun_fixed_iff
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
  {k : ℤ}
  {v : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  d.affineReflFun α k v = v ↔ ⟪α, v⟫_ℝ = ↑k := by
-- proof
  simp only [affineReflFun]
  constructor
  · intro h
    have h1 : (⟪α, v⟫_ℝ - ↑k) • d.coroot α = 0 := by
      have h2 : v - (⟪α, v⟫_ℝ - ↑k) • d.coroot α - v = 0 := by rw [h, sub_self]
      rwa [sub_right_comm, sub_self, zero_sub, neg_eq_zero] at h2
    have hcr_ne : d.coroot α ≠ 0 := by
      rw [d.coroot_def α hα]
      intro hc
      obtain h1 | h1 := smul_eq_zero.mp hc
      · exact div_ne_zero two_ne_zero (inner_self_ne_zero.mpr (d.roots_ne_zero α hα)) h1
      · exact d.roots_ne_zero α hα h1
    exact sub_eq_zero.mp ((smul_eq_zero.mp h1).resolve_right hcr_ne)
  · intro h
    simp [h, sub_self, zero_smul, sub_zero]

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[affineWeylGroup_uniqueDecomposition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma affineWeylGroup_uniqueDecomposition
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {w₁ w₂ : E ≃ₗᵢ[ℝ] E}
  {t₁ t₂ : E}
-- given
  (h : ∀ v : E, w₁ v + t₁ = w₂ v + t₂) :
-- imply
  w₁ = w₂ ∧ t₁ = t₂ := by
-- proof
  have h0 : ∀ v : E, (w₂.symm.trans w₁) v = v + (t₂ - t₁) := by
    intro v
    have hv := h (w₂.symm v)
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply] at hv ⊢
    have : w₁ (w₂.symm v) + t₁ + (-t₁) = v + t₂ + (-t₁) := congr_arg (· + (-t₁)) hv
    simp only [add_neg_cancel_right] at this
    rw [this]; abel
  have key := linear_inter_translation_trivial (w₂.symm.trans w₁) (t₂ - t₁) h0
  constructor
  ·
    have hw : w₂.symm.trans w₁ = 1 := key.2
    ext v
    have hv := LinearIsometryEquiv.ext_iff.mp hw (w₂ v)
    simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
      LinearIsometryEquiv.coe_one, id_eq] at hv
    exact hv
  ·
    have ht : t₂ - t₁ = 0 := key.1
    exact (sub_eq_zero.mp ht).symm

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[corootTranslation_eq_comp_affineRefls](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma corootTranslation_eq_comp_affineRefls
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
  rw [← d.linearRefl_eq_affineRefl_zero α v]
  exact d.translation_coroot_eq_comp α hα v

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[neg_corootTranslation_eq_comp_affineRefls](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma neg_corootTranslation_eq_comp_affineRefls
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E}
  {α : E}
-- given
  (hα : α ∈ d.roots) :
-- imply
  ∀ v : E, v - d.coroot α = d.affineReflFun α (-1) (d.affineReflFun α 0 v) := by
-- proof
  intro v
  rw [← d.linearRefl_eq_affineRefl_zero α v]
  simp only [affineReflFun, linearReflFun]
  have h_inner : ⟪α, d.coroot α⟫_ℝ = 2 := by
    rw [d.coroot_def α hα, inner_smul_right, div_mul_cancel₀]
    exact (inner_self_ne_zero.mpr (d.roots_ne_zero α hα))
  simp only [inner_sub_right, inner_smul_right, h_inner]
  push_cast
  module

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[reflections_generate_affineWeylGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma reflections_generate_affineWeylGroup
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  (∀ α ∈ d.roots, ∀ v : E, d.linearReflFun α v = d.affineReflFun α 0 v) ∧ (∀ α ∈ d.roots, ∀ v : E, v + d.coroot α = d.affineReflFun α 1 (d.affineReflFun α 0 v)) ∧ (∀ α ∈ d.roots, ∀ v : E, v - d.coroot α = d.affineReflFun α (-1) (d.affineReflFun α 0 v)) ∧ (∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E, d.affineReflFun α k v = d.linearReflFun α v + (k : ℝ) • d.coroot α) := by
-- proof
  exact ⟨
    fun α _ v => d.linearRefl_eq_affineRefl_zero α v,
    fun α hα v => d.corootTranslation_eq_comp_affineRefls α hα v,
    fun α hα v => d.neg_corootTranslation_eq_comp_affineRefls α hα v,
    fun α hα k v => d.affineRefl_eq_translation_comp_linearRefl α hα k v⟩

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[proposition_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma proposition_locallyFinite
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  d.affineArr.IsLocallyFinite :=
-- proof
  d.locallyFinite

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[proposition_semidirectProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma proposition_semidirectProduct
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  (∀ α ∈ d.roots, ∀ k : ℤ, ∀ v : E, ∃ (t : E), t ∈ d.corootLattice ∧ d.affineReflFun α k v = d.linearReflFun α v + t) ∧ (∀ w ∈ d.weylGroup, ∀ v ∈ d.corootLattice, (w : E ≃ₗᵢ[ℝ] E) v ∈ d.corootLattice) ∧ (∀ (w : E ≃ₗᵢ[ℝ] E) (t : E), (∀ v : E, w v = v + t) → t = 0 ∧ w = 1) :=
-- proof
  ⟨d.semidirect_product_affineWeylGroup,
    d.weylGroup_normalizes_lattice,
    linear_inter_translation_trivial⟩

end AffineWeylGroupFullData

namespace AffineWeylGroupFullData

/--
[proposition_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroupConstruction.lean)
-/
@[path]
lemma proposition_stable
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]
  {d : AffineWeylGroupFullData E} :
-- imply
  (∀ v ∈ d.corootLattice, ∀ η ∈ d.affineArr.hyperplanes, ∃ η' ∈ d.affineArr.hyperplanes, η'.normal = η.normal ∧ ∀ x : E, x ∈ η'.carrier ↔ (x - v) ∈ η.carrier) ∧ (∀ w ∈ d.weylGroup, ∀ η ∈ d.affineArr.hyperplanes, ∃ η' ∈ d.affineArr.hyperplanes, η'.normal = (w : E ≃ₗᵢ[ℝ] E) η.normal ∧ η'.offset = η.offset) :=
-- proof
  ⟨d.stable_corootLattice, d.stable_weylGroup⟩

end AffineWeylGroupFullData


-- created on 2026-10-23
