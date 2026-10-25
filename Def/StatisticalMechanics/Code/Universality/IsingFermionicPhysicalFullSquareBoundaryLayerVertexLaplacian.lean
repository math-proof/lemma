/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryLayerVertexLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerLaplacian


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fullVertexNorthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .north) :=
  fkIsingSquareDirectionEdge n x .north h

def fullVertexEastEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .east) :=
  fkIsingSquareDirectionEdge n x .east h

def fullVertexSouthEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .south) :=
  fkIsingSquareDirectionEdge n x .south h

def fullVertexWestEdge (n : Nat)
    (x : (fkSquareBoxPlanar n).V)
    (h : fkIsingSquareDirectionAvailable n x .west) :=
  fkIsingSquareDirectionEdge n x .west h

end
end StatMech.Universality
