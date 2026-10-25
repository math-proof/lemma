/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.Part3


namespace StatMech.FrontierD

theorem sixVertexFourByTwo_not_synchronizedActiveStepColorInvariant :
    ¬ SixVertexFourByTwoSynchronizedActiveStepColorInvariant := by
  classical
  intro hactive
  have hinvariant :=
    sixVertexDegreeTwoSynchronizedComponentSlotColorInvariant_of_active
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent hactive
  let x : DoubledAlignedState sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
    (sixVertexFourByTwoOrientedSeed, false)
  let returned :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalReturnState
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent false x
  let targetPairing :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalTargetPairing
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent false
  let coordinate := fkColoredBlackDartStrandSlotEquiv targetPairing
  let slot : sixVertexFourByTwoTorus.Vertex × Bool :=
    (doubledAlignedVertex x,
      doubledAlignedSlot sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false x)
  let dart : FKMedialBlackDart sixVertexFourByTwoTorus :=
    coordinate.symm slot
  have hslot : coordinate dart = slot := coordinate.apply_symm_apply slot
  have hdartActive : activeBlackDart
      (omega := sixVertexFourByTwoLowArrows)
      (eta := sixVertexFourByTwoHighArrows) dart := by
    unfold activeBlackDart
    rw [card_sixVertexLocalDisagreementSides]
    exact sixVertexFourByTwo_localDisagreementDegree_two dart.1.1
  have hstepActive : activeBlackDart
      (omega := sixVertexFourByTwoLowArrows)
      (eta := sixVertexFourByTwoHighArrows)
      (fkMedialBlackBoundaryPerm targetPairing dart) := by
    unfold activeBlackDart
    rw [card_sixVertexLocalDisagreementSides]
    exact sixVertexFourByTwo_localDisagreementDegree_two _
  have hfirst :
      (finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := sixVertexFourByTwoLowArrows)
          (eta := sixVertexFourByTwoHighArrows))
        ⟨dart, hdartActive⟩).1 =
      fkMedialBlackBoundaryPerm targetPairing dart :=
    finiteFirstReturn_eq_step_of_selected_step
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := sixVertexFourByTwoLowArrows)
        (eta := sixVertexFourByTwoHighArrows))
      ⟨dart, hdartActive⟩ hstepActive
  have hreturnSlot :=
    sixVertexDegreeTwoSynchronizedComponentPhysicalFirstReturn_slot
      sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
      sixVertexFourByTwo_locallyDegreeTwo
      sixVertexFourByTwoSynchronizedSeedComponent false x dart hdartActive
      hslot
  change coordinate
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := sixVertexFourByTwoLowArrows)
          (eta := sixVertexFourByTwoHighArrows))
        ⟨dart, hdartActive⟩).1) =
    (doubledAlignedVertex returned,
      doubledAlignedSlot sixVertexFourByTwoLowArrows_ice
        sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo false returned) at hreturnSlot
  rw [hfirst] at hreturnSlot
  have hboundaryCoordinate :
      fkColoredStrandSlotBoundaryPerm targetPairing slot =
        (doubledAlignedVertex returned,
          doubledAlignedSlot sixVertexFourByTwoLowArrows_ice
            sixVertexFourByTwoHighArrows_ice
            sixVertexFourByTwo_locallyDegreeTwo false returned) := by
    change coordinate
      (fkMedialBlackBoundaryPerm targetPairing (coordinate.symm slot)) = _
    change coordinate (fkMedialBlackBoundaryPerm targetPairing dart) = _
    exact hreturnSlot
  have hcolor := hinvariant (false, slot)
  rw [fkColoredLayeredStrandSlotBoundaryPerm_apply,
    hboundaryCoordinate] at hcolor
  change
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false returned =
      sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor
        sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
        sixVertexFourByTwo_locallyDegreeTwo
        sixVertexFourByTwoSynchronizedSeedComponent false x at hcolor
  dsimp only [returned, x] at hcolor
  rw [sixVertexFourByTwoPhysicalReturn_seed,
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq,
    sixVertexDegreeTwoSynchronizedComponentTransportedActiveColor_eq] at hcolor
  simp at hcolor

end StatMech.FrontierD
