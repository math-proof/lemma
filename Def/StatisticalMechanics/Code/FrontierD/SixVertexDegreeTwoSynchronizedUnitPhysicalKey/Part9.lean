/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part9


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent) :
    Equiv.Perm (FKLayeredStrandSlot T) :=
  fkIndexedOccurrenceSlotEquiv
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component))
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree
      component)
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
      heta hdegree component)

end
end StatMech.FrontierD
