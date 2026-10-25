/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedUnitPhysicalKey.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitSelector.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part13


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoSynchronizedComponentTransportedColor_firstReturn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (component :
      (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent)
    (hreturn :
      SixVertexDegreeTwoSynchronizedComponentActiveReturnColorInvariant homega
        heta hdegree component)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
      (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega heta
        hdegree component layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm
        (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing homega
          heta hdegree component layer))
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
              homega heta hdegree component layer) arrival)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv homega heta
          hdegree component
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
              homega heta hdegree component layer) dart)) := by
  dsimp only
  rw [sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot homega
      heta hdegree component layer x dart hactive hslot,
    hslot]
  exact hreturn layer x

end
end StatMech.FrontierD
