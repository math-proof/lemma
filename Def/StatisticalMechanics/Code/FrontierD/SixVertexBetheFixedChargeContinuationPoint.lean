/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeContinuationPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeEventualPerron
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheUniqueStabilitySheet
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexFixedChargeBetheContinuationPoint
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (r k : Nat) : SixVertexBetheContinuationSpace a b
      (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  let p := sixVertexFixedChargeBetheRoots hc2 r k
  refine ⟨(c, p), hc, ?_, ?_⟩
  · exact (sixVertexFixedChargeBetheRoots_mem_open hc2 r k).toClosed
  · exact (sixVertexBetheUpdate_eq_self_iff (sixVertexFourWidth_pos r k) p).mpr
      (sixVertexFixedChargeBetheRoots_is_solution hc2 r k)

end
end StatMech.FrontierD
