/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullCoordinateOneForm

theorem coordinatePrimitive_horizontal_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q) :
    A.coordinatePrimitive (q.1 + 1, q.2) - A.coordinatePrimitive q =
      A.horizontal q := by
  unfold coordinatePrimitive
  rw [FKIsingSquareFullIntegratedPrimitive.coordinateIndex_east n q hq]
  have h := A.primitiveNat_horizontal_increment
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).1
    (FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q).2
  simpa [horizontalNat,
    FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate_coordinateIndex
      n q hq] using h

theorem coordinatePrimitive_vertical_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (q : Int × Int)
    (hq : FKIsingSquareFullDiamond n q)
    (hqN : FKIsingSquareFullDiamond n (q.1, q.2 + 1)) :
    A.coordinatePrimitive (q.1, q.2 + 1) - A.coordinatePrimitive q =
      A.vertical q := by
  let ij := FKIsingSquareFullIntegratedPrimitive.coordinateIndex n q
  have hshift : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n ij.1 ij.2 = q :=
    FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate_coordinateIndex
      n q hq
  have hshiftN : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n ij.1 (ij.2 + 1) = (q.1, q.2 + 1) := by
    have hy : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
        n ij.1 (ij.2 + 1) =
      ((FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
        n ij.1 ij.2).1,
       (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
        n ij.1 ij.2).2 + 1) := by
      apply Prod.ext <;>
        simp [FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate] <;>
        omega
    rw [hy, hshift]
  unfold coordinatePrimitive
  rw [FKIsingSquareFullIntegratedPrimitive.coordinateIndex_north n q hq]
  have h := A.primitiveNat_vertical_increment ij.1 ij.2
    (hshift ▸ hq) (hshiftN ▸ hqN)
  simpa [ij, verticalNat, hshift] using h

end FKIsingSquareFullCoordinateOneForm
end
end StatMech.Universality
