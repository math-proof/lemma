/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part8


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem endpointCombinedSummand_at_label
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (j : Fin 3) {ts : List ℤ}
    (hend : (ofTurns a h0 ts).EndsAt (labelMid v du j)) :
    endpointCombinedSummand region a h0 v du ts =
      (labelMid v du j - v) *
        endpointParafSummand region a h0 (labelMid v du j)
          (5 / 8) hexChi ts := by
  fin_cases j
  · simpa [labelMid] using endpointCombinedSummand_at_p
      (region := region) (a := a) (h0 := h0) (v := v) (du := du)
      hdu hend
  · simpa [labelMid] using endpointCombinedSummand_at_q
      (region := region) (a := a) (h0 := h0) (v := v) (du := du)
      hdu hend
  · simpa [labelMid] using endpointCombinedSummand_at_r
      (region := region) (a := a) (h0 := h0) (v := v) (du := du)
      hdu hend


end
end StatMech.Universality
