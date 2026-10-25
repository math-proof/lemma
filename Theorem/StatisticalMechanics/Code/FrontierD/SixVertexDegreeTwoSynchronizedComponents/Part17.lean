/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part6


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem
    SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget.preservesTotalC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (supported :
      SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget seed) :
    supported.target.colorSplice.PreservesTotalC := by
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← supported.target.colorSplice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount]
  have htotal := sixVertexPairAtMostTwoCycleFineRelated_totalC
    ⟨supported.twoCycle, supported.fine.symm⟩
  simpa [fkColoredLoopPairingPairTotalC] using htotal.symm


end
end StatMech.FrontierD
