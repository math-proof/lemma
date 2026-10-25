/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoBranchClosedPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive.Part9


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoBranchClosedUnitPrefix_tauAdjusted_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree x ∈
        sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle ↔
      x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
        middle homegaSector hetaSector hmiddle := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · simp [sixVertexDegreeTwoTauAdjustedState, retie, heq]
  · rw [sixVertexDegreeTwoTauAdjustedState, if_neg heq]
    exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle x


end
end StatMech.FrontierD
