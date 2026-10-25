/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIncidence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidenceFiber
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part4
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIncidence


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareFullRadialNodeCoordinate
    (n : Nat) : FKIsingSquareFullRadialNode n → Int × Int
  | .inl x => fkIsingSquareFullVertexCoordinate n x
  | .inr c => fkIsingSquareFullFaceCoordinate n c

end
end StatMech.Universality
