/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Structure.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part2


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def SixVertexDegreeTwoSynchronizedSplitColorTarget.toSplice
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component}
    (target : SixVertexDegreeTwoSynchronizedSplitColorTarget seed) :
    FKColoredStrandSplice
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  fkColoredSlotColorInvariantSplice
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    target.pairing
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)
    target.slotColorInvariant


end
end StatMech.FrontierD
