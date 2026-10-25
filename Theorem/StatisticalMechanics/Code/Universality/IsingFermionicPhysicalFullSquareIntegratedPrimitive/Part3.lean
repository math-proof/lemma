/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareIntegratedPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegration.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquarePrimitive.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalGhostEnergy
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part3


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem coordinatePrimitive_horizontal_increment
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q) :
    coordinatePrimitive n hn (q.1 + 1, q.2) - coordinatePrimitive n hn q =
      fkIsingSquareFullHorizontalIncrement n hn q := by
  unfold coordinatePrimitive
  rw [coordinateIndex_east n q hq]
  have h := primitiveNat_horizontal_increment n hn
    (coordinateIndex n q).1 (coordinateIndex n q).2
  simpa [horizontalNat, shiftedCoordinate_coordinateIndex n q hq] using h

theorem coordinatePrimitive_vertical_increment
    (n : Nat) (hn : 0 < n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q)
    (hqN : FKIsingSquareFullDiamond n (q.1, q.2 + 1)) :
    coordinatePrimitive n hn (q.1, q.2 + 1) - coordinatePrimitive n hn q =
      fkIsingSquareFullVerticalIncrement n hn q := by
  let ij := coordinateIndex n q
  have hshift : shiftedCoordinate n ij.1 ij.2 = q :=
    shiftedCoordinate_coordinateIndex n q hq
  have hshiftN : shiftedCoordinate n ij.1 (ij.2 + 1) = (q.1, q.2 + 1) := by
    have hy : shiftedCoordinate n ij.1 (ij.2 + 1) =
        ((shiftedCoordinate n ij.1 ij.2).1,
          (shiftedCoordinate n ij.1 ij.2).2 + 1) := by
      apply Prod.ext <;> simp [shiftedCoordinate] <;> omega
    rw [hy, hshift]
  unfold coordinatePrimitive
  rw [coordinateIndex_north n q hq]
  have h := primitiveNat_vertical_increment n hn ij.1 ij.2
    (hshift ▸ hq) (hshiftN ▸ hqN)
  simpa [ij, verticalNat, hshift] using h

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
