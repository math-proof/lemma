/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part12


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexDegreeTwoSynchronizedComponentSpliceOfActive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T),
      activeBlackDart (omega := omega) (eta := eta) dart ∨
        activeBlackDart (omega := omega) (eta := eta)
          (alignedBoundaryPerm homega heta hdegree false dart) →
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
                homega heta hdegree component layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
            hdegree component
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredStrandSplice
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) :=
  fkColoredSlotColorInvariantSplice
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
      hdegree component)
    (Fintype.card
      (SixVertexDegreeTwoSynchronizedComponentBoundaryOccurrence homega heta
        hdegree component))
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey homega heta hdegree
      component)
    (sixVertexDegreeTwoSynchronizedComponentBoundaryFinKey_injective homega
      heta hdegree component)
    (sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active homega
      heta hdegree component hactive)


end
end StatMech.FrontierD
