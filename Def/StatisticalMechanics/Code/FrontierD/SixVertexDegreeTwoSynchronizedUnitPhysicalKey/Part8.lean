/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (layer : Bool)
    (i : Fin (Fintype.card
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component))) : T.Vertex × Bool :=
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer
    ((Fintype.equivFin
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component)).symm i).1

end
end StatMech.FrontierD
