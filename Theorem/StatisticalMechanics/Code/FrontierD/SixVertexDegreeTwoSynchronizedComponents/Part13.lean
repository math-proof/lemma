/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part11


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary_intertwining
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (slot : FKLayeredStrandSlot T) :
    seed.occurrenceEquiv (seed.desiredTargetBoundary slot) =
      fkColoredLayeredStrandSlotBoundaryPerm
        (fun layer =>
          ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
            layer).pairing)
        (seed.occurrenceEquiv slot) := by
  simp [SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary,
    Equiv.trans_apply]


end
end StatMech.FrontierD
