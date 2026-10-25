/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part7
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayer


namespace StatMech.Universality

open Finset Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareBoundaryDeletedPlanar (n : Nat) : PlanarZ2Subgraph where
  V := (fkSquareBoxPlanar n).V
  finV := inferInstance
  decV := inferInstance
  G := (fkSquareBoxPlanar n).G.deleteEdges
    (fkIsingSquarePerimeterPrimalEdgeFinset n :
      Set (Sym2 (fkSquareBoxPlanar n).V))
  emb := (fkSquareBoxPlanar n).emb
  isSub := by
    intro x y hxy
    exact (fkSquareBoxPlanar n).isSub hxy.1


def fkIsingSquareBoundaryLayerInwardSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .west
  | .top | .left => .east


def fkIsingSquareBoundaryLayerEndpointSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .south
  | .top | .left => .north


def fkIsingSquareBoundaryLayerComplementInwardSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .east
  | .top | .left => .west

def fkIsingSquareBoundaryLayerComplementEndpointSide :
    FKIsingSquareBoundarySide -> FKIsingMedialSide
  | .bottom | .right => .north
  | .top | .left => .south

end
end StatMech.Universality
