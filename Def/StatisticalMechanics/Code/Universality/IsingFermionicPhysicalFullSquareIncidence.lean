/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareFullVertexCoordinate
    (n : Nat) (x : FKIsingSquareFullVertexNode n) :
    Int × Int := (x.1 0 + x.1 1, x.1 0 - x.1 1)

def fkIsingSquareFullFaceCoordinate
    (n : Nat) (c : FKIsingSquareFullFaceNode n) :
    Int × Int :=
  let p := fkIsingSquareInteriorCellKey n c
  (p.1 + p.2 + 1, p.1 - p.2)

end
end StatMech.Universality
