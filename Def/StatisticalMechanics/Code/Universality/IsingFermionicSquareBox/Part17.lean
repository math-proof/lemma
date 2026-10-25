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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part18


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareDirectionEdge (n : Nat)
    (u : (fkSquareBoxPlanar n).V) (d : FKIsingSquareDirection)
    (hd : fkIsingSquareDirectionAvailable n u d) :
    FKIsingMedialVertex (fkSquareBoxPlanar n) :=
  ⟨s(u, fkIsingSquareNeighbor n u d hd),
    (SimpleGraph.mem_edgeSet _).2 (fkIsingSquare_adj_neighbor n u d hd)⟩


def fkIsingSquareDartDirection (n : Nat)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    FKIsingSquareDirection :=
  match (fkIsingSquareOrientedEdge n d.1).axis,
      (fkIsingSquareSideCorner d.2).1 with
  | .horizontal, .tail => .east
  | .horizontal, .head => .west
  | .vertical, .tail => .north
  | .vertical, .head => .south


end
end StatMech.Universality
