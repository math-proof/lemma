/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareFaceLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareLaplacian.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part7


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def faceNorthNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : c.2.1 + 1 < 2 * n) : FKIsingSquareFullFaceNode n :=
  (c.1, ⟨c.2.1 + 1, h⟩)

def faceEastNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : c.1.1 + 1 < 2 * n) : FKIsingSquareFullFaceNode n :=
  (⟨c.1.1 + 1, h⟩, c.2)

def faceSouthNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.2.1) : FKIsingSquareFullFaceNode n :=
  (c.1, ⟨c.2.1 - 1, by omega⟩)

def faceWestNeighbor (n : Nat) (c : FKIsingSquareFullFaceNode n)
    (h : 0 < c.1.1) : FKIsingSquareFullFaceNode n :=
  (⟨c.1.1 - 1, by omega⟩, c.2)

end
end StatMech.Universality
