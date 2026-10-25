/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part8


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

namespace HLHDTaggedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N extra : ℕ}

theorem sum_eq_pairImage
    (H : HLHDTaggedTwoHalfData a h0 N extra) (x : ℝ) :
    ∑ d : hhc_Dn a h0 N,
        hhc_halfWeight x (H.lowerHalf d) *
          hhc_halfWeight x (H.upperHalf d) =
      ∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
  classical
  rw [pairImage, Finset.sum_image
    (fun d _ e _ hde => H.contentPair_injective hde)]
  rfl

theorem pairImage_subset_product
    (H : HLHDTaggedTwoHalfData a h0 N extra) :
    H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
  classical
  intro p hp
  rw [pairImage, Finset.mem_image] at hp
  obtain ⟨d, _, rfl⟩ := hp
  rw [Finset.mem_product]
  exact ⟨Finset.mem_image_of_mem H.lowerHalf (Finset.mem_univ d),
    Finset.mem_image_of_mem H.upperHalf (Finset.mem_univ d)⟩

theorem pair_sum_le_product
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 ≤ x) :
    (∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
  classical
  calc
    (∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤
        ∑ p ∈ H.lowerImage ×ˢ H.upperImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg H.pairImage_subset_product
        (fun p _ _ => mul_nonneg (hhc_halfWeight_nonneg hx p.1)
          (hhc_halfWeight_nonneg hx p.2))
    _ = (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]


theorem finite_partial_bound
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ extra)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) := by
  rw [← hhc_partial_eq a h0 x N]
  calc
    (∑ d : hhc_Dn a h0 N, x ^ d.1.length) =
        (x ^ extra)⁻¹ *
          ∑ d : hhc_Dn a h0 N,
            hhc_halfWeight x (H.lowerHalf d) *
              hhc_halfWeight x (H.upperHalf d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact H.source_weight_factor x hx d
    _ = (x ^ extra)⁻¹ *
        ∑ p ∈ H.pairImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
      rw [H.sum_eq_pairImage x]
    _ ≤ (x ^ extra)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      mul_le_mul_of_nonneg_left (H.pair_sum_le_product hx.le)
        (inv_nonneg.mpr (pow_nonneg hx.le _))


theorem finite_partial_bound_tagged
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x < hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ extra)⁻¹ *
        (∏' T, (1 + hlhdt_taggedMajorant x T)) ^ 2 := by
  let P := ∏' T, (1 + hlhdt_taggedMajorant x T)
  have hlo :
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) ≤ P := by
    simpa only [lowerImage, P] using
      hlhdt_contentHalfImage_sum_le_tprod
        (hhc_Dn a h0 N) H.lower H.lower_legal H.lower_halfSpace
        hx hxone hxchi hlocal hwindow
  have hup :
      (∑ s ∈ H.upperImage, hhc_halfWeight x s) ≤ P := by
    simpa only [upperImage, P] using
      hlhdt_contentHalfImage_sum_le_tprod
        (hhc_Dn a h0 N) H.upper H.upper_legal H.upper_halfSpace
        hx hxone hxchi hlocal hwindow
  have hupper_nn :
      0 ≤ ∑ s ∈ H.upperImage, hhc_halfWeight x s :=
    Finset.sum_nonneg fun s _ => hhc_halfWeight_nonneg hx.le s
  have hmul : Multipliable
      (fun T => 1 + hlhdt_taggedMajorant x T) :=
    hex_bridge_multipliable _ (hlhdt_taggedMajorant_summable hx hxchi)
  have hP_one : 1 ≤ P := by
    have h := hexSeams_prod_one_add_le_tprod
      (hlhdt_taggedMajorant x) (hlhdt_taggedMajorant_nonneg hx.le) hmul 0
    simpa [P] using h
  calc
    (∑ n ∈ Finset.range N,
        (hlc_sawCount a h0 n : ℝ) * x ^ n) ≤
        (x ^ extra)⁻¹ *
          ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
            (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      H.finite_partial_bound hx
    _ ≤ (x ^ extra)⁻¹ * (P * P) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul hlo hup hupper_nn (le_trans (by norm_num) hP_one)
      · positivity
    _ = (x ^ extra)⁻¹ * P ^ 2 := by ring


theorem summable_of_taggedTwoHalfData
    (H : ∀ N, HLHDTaggedTwoHalfData a h0 N extra)
    {x : ℝ} (hx : 0 < x) (hxone : x ≤ 1) (hxchi : x < hexChiE)
    (hlocal : ∀ T (hT : 0 < T) L, HexCSLocalRelation T L hT)
    (hwindow : ∀ T (hT : 0 < T) L, HexCSBoundaryWindowLaw T L hT) :
    Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
  apply summable_of_sum_range_le
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.le _)
  · intro N
    simpa [hlc_sawCountR] using
      (H N).finite_partial_bound_tagged hx hxone hxchi hlocal hwindow

end HLHDTaggedTwoHalfData
end
end StatMech.Universality
