/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part2


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceNorthEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceNWVertex n c) .east
    (faceNW_east_available n c)

def faceEastEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceSEVertex n c) .north
    (faceSE_north_available n c)

def faceSouthEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceSWVertex n c) .east
    (faceSW_east_available n c)

def faceWestEdge (n : Nat) (c : FKIsingSquareFullFaceNode n) :=
  fkIsingSquareDirectionEdge n (faceSWVertex n c) .north
    (faceSW_north_available n c)

end
end StatMech.Universality
