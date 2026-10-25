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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part35


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquareDirection.eighthTurn : FKIsingSquareDirection -> Int
  | .east => 0
  | .north => 2
  | .west => 4
  | .south => 6


def fkIsingSquareCornerTangentCode
    (d : FKIsingSquareDirection) (turn : FKIsingSquareCornerTurn) : Int :=
  d.eighthTurn + match turn with
    | .counterclockwise => 3
    | .clockwise => 5


def fkIsingSquareCarrierTangentCode (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> Int
  | .dart d => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n d) (fkIsingSquareSideCorner d.2).2
  | .source => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n
        (fkIsingSquareSourceInteriorDart n hn))
      (fkIsingSquareSideCorner
        (fkIsingSquareSourceInteriorDart n hn).2).2 + 4
  | .terminal => fkIsingSquareCornerTangentCode
      (fkIsingSquareDartDirection n
        (fkIsingSquareTerminalInteriorDart n hn))
      (fkIsingSquareSideCorner
        (fkIsingSquareTerminalInteriorDart n hn).2).2


def fkIsingSquareSignedEighthTurn (a b : Int) : Int :=
  (b - a + 4) % 8 - 4


def fkIsingSquareExteriorCutStart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareBondMate n hn (fkIsingSquareSourceInteriorDart n hn)

def fkIsingSquareExteriorCutEnd (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  fkIsingSquareBondMate n hn (fkIsingSquareTerminalInteriorDart n hn)

end
end StatMech.Universality
