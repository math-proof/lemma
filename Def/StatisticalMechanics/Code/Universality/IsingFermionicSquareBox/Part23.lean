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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part24


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareSourceInteriorDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquareSourcePrimalEdge n hn, .west)


def fkIsingSquareTerminalInteriorDart (n : Nat) (hn : 0 < n) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquareTerminalPrimalEdge n hn, .north)


noncomputable def fkIsingSquareCutBondMate (n : Nat) (hn : 0 < n) :
    FKIsingSquareMedialCarrier n -> FKIsingSquareMedialCarrier n
  | .source => .dart (fkIsingSquareSourceInteriorDart n hn)
  | .terminal => .dart (fkIsingSquareTerminalInteriorDart n hn)
  | .dart d =>
      if d = fkIsingSquareSourceInteriorDart n hn then .source
      else if d = fkIsingSquareTerminalInteriorDart n hn then .terminal
      else if d = fkIsingSquareBondMate n hn
          (fkIsingSquareSourceInteriorDart n hn) then
        .dart (fkIsingSquareBondMate n hn
          (fkIsingSquareTerminalInteriorDart n hn))
      else if d = fkIsingSquareBondMate n hn
          (fkIsingSquareTerminalInteriorDart n hn) then
        .dart (fkIsingSquareBondMate n hn
          (fkIsingSquareSourceInteriorDart n hn))
      else .dart (fkIsingSquareBondMate n hn d)

end
end StatMech.Universality
