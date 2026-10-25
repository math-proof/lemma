/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialIncidence.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalEnergy
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPrimitiveFiniteIntegration
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialRectangle.Part4


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

structure FKIsingSquareInteriorRadialFiniteRectanglePlacement
    (n : Nat) (hn : 0 < n) (width height : Nat) where
  horizontal : Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn
  vertical : Nat → Nat → FKIsingSquareInteriorRadialIncidence n hn
  cell : Fin width → Fin height → FKIsingSquareInteriorRadialCell n
  west : ∀ i j, vertical i.1 j.1 =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .west
  east : ∀ i j, horizontal i.1 (j.1 + 1) =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .east
  south : ∀ i j, horizontal i.1 j.1 =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .south
  north : ∀ i j, vertical (i.1 + 1) j.1 =
    fkIsingSquareInteriorRadialCellIncidence n hn (cell i j) .north

end
end StatMech.Universality
