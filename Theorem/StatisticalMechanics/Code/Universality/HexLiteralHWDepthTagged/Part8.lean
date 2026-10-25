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
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepthTagged.Part7


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

namespace HLHDTaggedTwoHalfData

variable {a : ℂ} {h0 : ℤ} {N extra : ℕ}

theorem source_weight_factor
    (H : HLHDTaggedTwoHalfData a h0 N extra)
    (x : ℝ) (hx : 0 < x) (d : hhc_Dn a h0 N) :
    x ^ d.1.length = (x ^ extra)⁻¹ *
      (hhc_halfWeight x (H.lowerHalf d) *
        hhc_halfWeight x (H.upperHalf d)) := by
  rw [hhc_halfWeight_eq_pow, hhc_halfWeight_eq_pow,
    H.lowerHalf_turns, H.upperHalf_turns, ← pow_add, H.length_add d,
    pow_add]
  have hpow : x ^ extra ≠ 0 := pow_ne_zero _ (ne_of_gt hx)
  calc
    x ^ d.1.length = 1 * x ^ d.1.length := by ring
    _ = ((x ^ extra)⁻¹ * x ^ extra) * x ^ d.1.length := by
      rw [inv_mul_cancel₀ hpow]
    _ = (x ^ extra)⁻¹ * (x ^ d.1.length * x ^ extra) := by ring

end HLHDTaggedTwoHalfData
end
end StatMech.Universality
