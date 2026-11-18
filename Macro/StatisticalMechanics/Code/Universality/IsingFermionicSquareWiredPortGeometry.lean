/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib


public meta section

namespace StatMech.Universality

noncomputable section

macro "south_coboundary_simp" : tactic =>
  `(tactic| simp_all (config := { maxSteps := 1000000 })
    [fkIsingSquareWiredMacroTurnCoboundaryAt,
      fkIsingSquareWiredMacroGauge,
      fkIsingSquareWiredPortMacroCodeWord,
      fkIsingSquareWiredPortMacroStepWord,
      fkIsingSquareWiredOrdinaryBondStepWord,
      fkIsingSquareWiredBondArcBase,
      fkIsingSquareWiredBondArcLength,
      fkIsingSquareBondMate,
      fkIsingSquarePreviousDirection,
      fkIsingSquareNextDirection,
      fkIsingSquareDirectionDart_endpoint,
      fkIsingSquareDirectionDart_direction,
      fkIsingSquareDirectionDart_turn,
      fkIsingSquareOrientedEdge_directionEdge,
      fkIsingSquareDirectionEdgeOrientation,
      fkIsingSquareWiredDartSlot,
      fkIsingSquareWiredPortSlot,
      fkIsingSquareWiredRingStepIndex,
      fkIsingSquareWiredUnitDiagonalReverse,
      fkIsingSquareWiredLocalStepIndex,
      fkIsingSquareWiredUnitDiagonalTangentCode,
      fkIsingSquareWiredPortNext,
      fkIsingSquareWiredBlackOfDart,
      fkIsingSquareWiredDirectedTangentCode,
      fkIsingSquareWiredObservationCorrection,
      fkIsingSquareWiredCarrierTangentCode,
      fkIsingSquareWiredTransitionMate,
      fkIsingSquareWiredTransitionTurn,
      fkIsingSquareWiredBondTurn,
      fkIsingSquareOrientedPrincipalBondTurn,
      fkIsingSquareCornerTangentCode,
      fkIsingSquareDartDirection,
      fkIsingSquareSideCorner,
      FKIsingMedialDart.localMate,
      FKIsingSquareDirection.eighthTurn,
      fkIsingSquareSignedEighthTurn,
      carrierAdjacentSum,
      Fin.add_def,
      Int.ModEq])

end
end StatMech.Universality
