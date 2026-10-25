/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part5


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HexHWContentDecomp

variable {D : Type}


section Finite

variable [Fintype D]


theorem sum_eq_pairImage (H : HexHWContentDecomp D) (x : ℝ) :
    ∑ d : D, x ^ (H.turns d).length =
      ∑ p ∈ H.pairImage,
        hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
  classical
  rw [pairImage, Finset.sum_image (fun a _ b _ hab => H.pair_injective hab)]
  apply Finset.sum_congr rfl
  intro d _
  exact H.weight_factor x d


theorem pairImage_subset_product (H : HexHWContentDecomp D) :
    H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
  classical
  intro p hp
  rw [pairImage, Finset.mem_image] at hp
  obtain ⟨d, _, rfl⟩ := hp
  rw [Finset.mem_product]
  exact ⟨Finset.mem_image_of_mem H.lower (Finset.mem_univ d),
    Finset.mem_image_of_mem H.upper (Finset.mem_univ d)⟩


theorem finite_content_bound (H : HexHWContentDecomp D) {x : ℝ} (hx : 0 ≤ x) :
    ∑ d : D, x ^ (H.turns d).length ≤
      (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
        (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
  classical
  rw [H.sum_eq_pairImage x]
  calc
    (∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2)
        ≤ ∑ p ∈ H.lowerImage ×ˢ H.upperImage,
            hhc_halfWeight x p.1 * hhc_halfWeight x p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg H.pairImage_subset_product
        (fun p _ _ => mul_nonneg (hhc_halfWeight_nonneg hx p.1)
          (hhc_halfWeight_nonneg hx p.2))
    _ = (∑ s ∈ H.lowerImage, hhc_halfWeight x s) *
          (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
      rw [Finset.sum_product]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]

end Finite
end HexHWContentDecomp
end StatMech.Universality
