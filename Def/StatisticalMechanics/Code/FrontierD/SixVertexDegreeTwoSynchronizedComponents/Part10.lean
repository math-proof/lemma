/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoBranchClosedPhysicalKey.Part6
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part11


namespace StatMech.FrontierD

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

noncomputable def sixVertexDegreeTwoSynchronizedSplitBoundaryEmbedding
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) (layer : Bool) :
    Fin (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) ↪
      T.Vertex × Bool :=
  ⟨sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer,
    sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed layer⟩


noncomputable def SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    {homega : omega.IceRule} {heta : eta.IceRule}
    {hdegree : SixVertexLocallyDegreeTwo omega eta}
    {component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
    (seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree
      component) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  fkIndexedOccurrenceSlotEquiv
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed))
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed)
    (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed)

end
end StatMech.FrontierD
