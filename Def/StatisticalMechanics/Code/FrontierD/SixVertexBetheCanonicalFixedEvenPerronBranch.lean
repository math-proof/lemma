/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedEvenPerronBranch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeContinuationPoint
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedEvenPerronBranch
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexCanonicalFixedEvenChargeContinuationPoint
    {a b c : Real} (ha : 2 < a) (hc : c ∈ Set.Icc a b)
    (s k : Nat) : SixVertexBetheContinuationSpace a b
      (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) := by
  let hc2 : 2 < c := ha.trans_le hc.1
  let p := sixVertexFixedEvenChargeBetheRoots hc2 s k
  refine ⟨(c, p), hc, ?_, ?_⟩
  · exact (sixVertexFixedEvenChargeRoots_mem_open_canonical hc2 s k).toClosed
  · exact (sixVertexBetheUpdate_eq_self_iff
      (sixVertexFourWidth_pos (2 * s) k) p).mpr
      (sixVertexFixedEvenChargeRoots_is_solution_canonical hc2 s k)

end
end StatMech.FrontierD
