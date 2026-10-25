/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part9


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

theorem sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)).symm.injective
  apply Subtype.ext
  unfold sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey at heq
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective heq
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective heq


end
end StatMech.FrontierD
