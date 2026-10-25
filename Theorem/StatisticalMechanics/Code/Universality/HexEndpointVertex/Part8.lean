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
import Structure.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem HexEndpointCyclicTriplet.contribution_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (C : HexEndpointCyclicTriplet region a h0 v du) :
    (labelMid v du C.baseLabel - v) *
        endpointParafSummand region a h0 (labelMid v du C.baseLabel)
          (5 / 8) hexChi C.base +
      (labelMid v du (hexCyclicSucc C.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicSucc C.baseLabel))
          (5 / 8) hexChi (C.base ++ [-1]) +
      (labelMid v du (hexCyclicPred C.baseLabel) - v) *
        endpointParafSummand region a h0
          (labelMid v du (hexCyclicPred C.baseLabel))
          (5 / 8) hexChi (C.base ++ [1]) = 0 := by
  let d : ℂ := labelMid v du C.baseLabel - v
  have hbase : v + d = labelMid v du C.baseLabel := by simp [d]
  have hsucc : v + hexOmega * d =
      labelMid v du (hexCyclicSucc C.baseLabel) := by
    simpa [d] using (hexCyclicSucc_mid v du C.baseLabel).symm
  have hpred : v + hexOmega ^ 2 * d =
      labelMid v du (hexCyclicPred C.baseLabel) := by
    simpa [d] using (hexCyclicPred_mid v du C.baseLabel).symm
  have hz := endpoint_genuine_triplet_zero region a h0 v d C.base
    (by simpa [hbase] using C.base_valid)
    (by simpa [hsucc] using C.succ_valid)
    (by simpa [hpred] using C.pred_valid)
  simpa [hbase, hsucc, hpred] using hz


end
end StatMech.Universality
