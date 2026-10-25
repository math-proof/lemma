/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part33


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

@[simp] theorem fkIsingSquareDartDirection_sourceInterior
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartDirection n
      (fkIsingSquareSourcePrimalEdge n hn, .west) =
      .east := by
  simp [fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_source,
    fkIsingSquareSourceEdgeOrientation]

@[simp] theorem fkIsingSquareDartDirection_terminalInterior
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareDartDirection n
      (fkIsingSquareTerminalPrimalEdge n hn, .north) =
      .south := by
  simp [fkIsingSquareDartDirection,
    fkIsingSquareSideCorner, fkIsingSquareOrientedEdge_terminal,
    fkIsingSquareTerminalEdgeOrientation]

@[simp] theorem fkIsingSquareCarrierTangentCode_exteriorCutStart
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierTangentCode n hn
      (.dart (fkIsingSquareExteriorCutStart n hn)) = 7 := by
  simp only [fkIsingSquareExteriorCutStart, fkIsingSquareBondMate,
    fkIsingSquareSourceInteriorDart, fkIsingSquareSideCorner]
  simp only [fkIsingSquareCarrierTangentCode,
    fkIsingSquareDirectionDart_direction, fkIsingSquareDirectionDart_turn,
    fkIsingSquareCornerTangentCode]
  rw [fkIsingSquareDartEndpoint_sourceAttachment,
    fkIsingSquareDartDirection_sourceInterior]
  simp [fkIsingSquareNextDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareMarkedA, FKIsingSquareDirection.eighthTurn, hn]

@[simp] theorem fkIsingSquareCarrierTangentCode_exteriorCutEnd
    (n : Nat) (hn : 0 < n) :
    fkIsingSquareCarrierTangentCode n hn
      (.dart (fkIsingSquareExteriorCutEnd n hn)) = 3 := by
  simp only [fkIsingSquareExteriorCutEnd, fkIsingSquareBondMate,
    fkIsingSquareTerminalInteriorDart, fkIsingSquareSideCorner]
  simp only [fkIsingSquareCarrierTangentCode,
    fkIsingSquareDirectionDart_direction, fkIsingSquareDirectionDart_turn,
    fkIsingSquareCornerTangentCode]
  rw [fkIsingSquareDartEndpoint_terminalAttachment,
    fkIsingSquareDartDirection_terminalInterior]
  simp [fkIsingSquarePreviousDirection, fkIsingSquareDirectionAvailable,
    fkIsingSquareMarkedB, FKIsingSquareDirection.eighthTurn, hn]


end
end StatMech.Universality
