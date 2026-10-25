/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part34


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

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
