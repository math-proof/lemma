/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part9
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectRawPrimalCrossingDevelopedExtremeDart_label
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectMedialDartPrimalLabel R
        (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side) =
      if side then fkRectRawPrimalCrossingTopVertex R omega X
      else fkRectRawPrimalCrossingBottomVertex R omega X := by
  cases side <;> simp [fkRectRawPrimalCrossingDevelopedExtremeDart]


theorem fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (side : Bool) :
    fkRectMedialComponentToPrimalComponent R omega
        ((fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X side)) =
      fkRectRawPrimalCrossingTorusComponent R omega X := by
  rw [fkRectMedialComponentToPrimalComponent_mk,
    fkRectRawPrimalCrossingDevelopedExtremeDart_label]
  cases side
  · exact (mem_fkRectRawPrimalCrossingTorusVertices R omega X _).1
      (fkRectRawPrimalCrossingBottomVertex_spec R omega X).1
  · exact (mem_fkRectRawPrimalCrossingTorusVertices R omega X _).1
      (fkRectRawPrimalCrossingTopVertex_spec R omega X).1


theorem fkRectRawPrimalCrossingDevelopedExtremeDart_matches_component
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (hX : X ∈ fkRectZeroTurnPrimalTouchedCrossings R omega C) :
    fkRectMedialComponentToPrimalComponent R omega
        ((fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
            (fkRectRawPrimalCrossingDevelopedExtremeDart R omega X
              (fkRectZeroTurnRemainderSide R omega C))) =
      fkRectZeroTurnRemainderPrimalComponent R omega C := by
  rw [fkRectRawPrimalCrossingDevelopedExtremeDart_primalComponent]
  exact fkRectZeroTurnPrimalTouchedCrossing_matches R omega C X hX


end
end StatMech.FrontierD
