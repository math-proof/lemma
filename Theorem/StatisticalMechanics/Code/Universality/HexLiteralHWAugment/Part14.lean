/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWAugment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14


namespace StatMech.Universality

open HexWalk


theorem hlha_finite_partial_bound (a : ℂ) (h0 : ℤ) (N : ℕ)
    {x : ℝ} (hx : 0 < x) :
    ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤
      (x ^ 2)⁻¹ *
        ((∑ s ∈ (hlha_augmentedTwoHalfData a h0 N).lowerImage,
            hhc_halfWeight x s) *
          (∑ s ∈ (hlha_augmentedTwoHalfData a h0 N).upperImage,
            hhc_halfWeight x s)) := by
  exact (hlha_augmentedTwoHalfData a h0 N).finite_partial_bound hx

end StatMech.Universality
