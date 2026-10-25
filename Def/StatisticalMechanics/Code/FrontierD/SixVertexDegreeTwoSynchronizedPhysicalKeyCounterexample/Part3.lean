/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.Part3


namespace StatMech.FrontierD

def SixVertexFourByTwoSynchronizedActiveStepColorInvariant : Prop :=
  ∀ (layer : Bool) (dart : FKMedialBlackDart sixVertexFourByTwoTorus),
    activeBlackDart (omega := sixVertexFourByTwoLowArrows)
        (eta := sixVertexFourByTwoHighArrows) dart ∨
      activeBlackDart (omega := sixVertexFourByTwoLowArrows)
        (eta := sixVertexFourByTwoHighArrows)
        (alignedBoundaryPerm sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo false dart) →
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo
          sixVertexFourByTwoSynchronizedSeedComponent
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            sixVertexFourByTwoLowArrows_ice
            sixVertexFourByTwoHighArrows_ice
            sixVertexFourByTwo_locallyDegreeTwo layer
            (sixVertexDegreeTwoSynchronizedComponentBoundaryFalseDart
              sixVertexFourByTwoLowArrows_ice
              sixVertexFourByTwoHighArrows_ice
              sixVertexFourByTwo_locallyDegreeTwo
              sixVertexFourByTwoSynchronizedSeedComponent layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo)
        (sixVertexDegreeTwoSynchronizedComponentOccurrenceEquiv
          sixVertexFourByTwoLowArrows_ice
          sixVertexFourByTwoHighArrows_ice
          sixVertexFourByTwo_locallyDegreeTwo
          sixVertexFourByTwoSynchronizedSeedComponent
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            sixVertexFourByTwoLowArrows_ice
            sixVertexFourByTwoHighArrows_ice
            sixVertexFourByTwo_locallyDegreeTwo layer dart))


end StatMech.FrontierD
