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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part20


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareEndpointForDirection :
    FKIsingSquareDirection -> FKIsingSquareEdgeEndpoint
  | .east | .north => .tail
  | .west | .south => .head


def fkIsingSquareDirectionDart (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d)
    (turn : FKIsingSquareCornerTurn) :
    FKIsingMedialDart (fkSquareBoxPlanar n) :=
  (fkIsingSquareDirectionEdge n u d hd,
    fkIsingSquareCornerSide (fkIsingSquareEndpointForDirection d, turn))

end
end StatMech.Universality
