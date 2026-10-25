/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part26


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HLHRAugmentedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N : ℕ}


theorem sum_eq_pairImage (H : HLHRAugmentedTwoHalfData a h0 N) (x : ℝ) :
    ∑ d : hhc_Dn a h0 N,
        hhc_halfWeight x (H.lowerHalf d) *
          hhc_halfWeight x (H.upperHalf d) =
      ∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
  classical
  rw [pairImage, Finset.sum_image
    (fun d _ e _ hde => H.contentPair_injective hde)]
  rfl


theorem pairImage_subset_product (H : HLHRAugmentedTwoHalfData a h0 N) :
    H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
  classical
  intro p hp
  rw [pairImage, Finset.mem_image] at hp
  obtain ⟨d, _, rfl⟩ := hp
  rw [Finset.mem_product]
  exact ⟨Finset.mem_image_of_mem H.lowerHalf (Finset.mem_univ d),
    Finset.mem_image_of_mem H.upperHalf (Finset.mem_univ d)⟩


theorem pair_sum_le_product (H : HLHRAugmentedTwoHalfData a h0 N)
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


theorem finite_partial_bound (H : HLHRAugmentedTwoHalfData a h0 N)
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ 2)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) := by
  rw [← hhc_partial_eq a h0 x N]
  calc
    (∑ d : hhc_Dn a h0 N, x ^ d.1.length) =
        (x ^ 2)⁻¹ *
          ∑ d : hhc_Dn a h0 N,
            hhc_halfWeight x (H.lowerHalf d) *
              hhc_halfWeight x (H.upperHalf d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact H.source_weight_factor x hx d
    _ = (x ^ 2)⁻¹ *
        ∑ p ∈ H.pairImage,
          hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
      rw [H.sum_eq_pairImage x]
    _ ≤ (x ^ 2)⁻¹ *
        ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s)) :=
      mul_le_mul_of_nonneg_left (H.pair_sum_le_product (le_of_lt hx))
        (by positivity)

end HLHRAugmentedTwoHalfData
end StatMech.Universality
