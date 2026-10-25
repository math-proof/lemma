/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedExtremeClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryPotentialContradiction
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part4
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence_of_regularNeighborhood
    (R : FKRectTorus) (omega : R.Configuration)
    (hregular : FKRectPrimalRankOneRegularNeighborhood R omega) :
    FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega := by
  intro C X hX hdisc
  let d := fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
    (fkRectZeroTurnRemainderSide R omega C)
  let e := fkRectZeroTurnRemainderOrientedDart R omega C
    (fkMedialCheckerColor d)
  have hnoNet : ¬ FKRectHasNet R omega :=
    not_fkRectHasNet_of_zeroTurnRemainder R omega C
  have heComponent : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk e =
      C.1 := by
    exact fkRectZeroTurnRemainderOrientedDart_component R omega C _
  have hfiber :
      fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              d) =
        fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              e) := by
    calc
      fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              d) = fkRectZeroTurnRemainderPrimalComponent R omega C := by
        exact fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component
          R omega C X hX
      _ = fkRectMedialComponentToPrimalComponent R omega
          ((fkMedialLoopGraph R.medialTorus
            (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
              e) := by
        unfold fkRectZeroTurnRemainderPrimalComponent
        rw [heComponent]
  have hcolor : fkMedialCheckerColor d = fkMedialCheckerColor e := by
    dsimp only [e]
    symm
    exact fkRectZeroTurnRemainderOrientedDart_checkerColor R omega C _
  have hdVertical : (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).2 = 0 :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C d
  have heVertical : (fkRectWalkWinding R
      (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).2 = 0 :=
    fkRectMedialBoundaryPrimalOrbitWalk_verticalWinding_eq_zero_of_remainder
      R omega C e
  have hsign : 0 < (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega d)).1 *
      (fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalOrbitWalk R omega e)).1 := by
    exact hregular.developedExtreme_sameSign C X hX hdisc
  calc
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
            (fkRectZeroTurnRemainderSide R omega C)) =
        (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            e := by
      exact hregular.sameSign_unique hnoNet d e hcolor hfiber hdVertical
        heVertical hsign
    _ = C.1 := heComponent


theorem fkRectZeroTurnPrimalDevelopedExtremeIncidence_of_disconnected
    (R : FKRectTorus) (omega : R.Configuration)
    (hdisconnected :
      FKRectZeroTurnPrimalDevelopedExtremeDisconnectedIncidence R omega) :
    FKRectZeroTurnPrimalDevelopedExtremeIncidence R omega := by
  intro C X hX
  by_cases hreach : (fkRectOpenGraph R omega).Reachable
      (fkRectMedialWestPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
      (fkRectMedialEastPrimal R
        (fkRectRawPrimalCrossingDevelopedExtremeEdge R omega X
          (fkRectZeroTurnRemainderSide R omega C)))
  · exact
      fkRectRawPrimalCrossingDevelopedExtreme_component_eq_of_endpointReachable
        R omega C X hX hreach
  · exact hdisconnected C X hX hreach

end
end StatMech.FrontierD
