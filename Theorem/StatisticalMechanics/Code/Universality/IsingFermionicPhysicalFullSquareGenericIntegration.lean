/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGenericIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part5
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGenericIntegration


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullCoordinateOneForm

theorem primitiveNat_horizontal_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat) :
    A.primitiveNat (i + 1) j - A.primitiveNat i j =
      A.horizontalNat i j := by
  exact isingCenteredPrimitive_horizontal_increment
    A.horizontalNat A.verticalNat (2 * n) i j

theorem primitiveNat_vertical_increment {n : Nat}
    (A : FKIsingSquareFullCoordinateOneForm n) (i j : Nat)
    (h0 : FKIsingSquareFullDiamond n
      (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i j))
    (h1 : FKIsingSquareFullDiamond n
      (FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n i (j + 1))) :
    A.primitiveNat i (j + 1) - A.primitiveNat i j =
      A.verticalNat i j := by
  apply isingCenteredPrimitive_vertical_increment
  intro k hk
  have hcell := FKIsingSquareFullIntegratedPrimitive.diamondCell_of_row_interval
    n i j k h0 h1 hk
  let q := FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate n k j
  have hx : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n (k + 1) j = (q.1 + 1, q.2) := by
    apply Prod.ext <;>
      simp [q, FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate] <;>
      omega
  have hy : FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate
      n k (j + 1) = (q.1, q.2 + 1) := by
    apply Prod.ext <;>
      simp [q, FKIsingSquareFullIntegratedPrimitive.shiftedCoordinate] <;>
      omega
  dsimp [horizontalNat, verticalNat]
  rw [hx, hy]
  exact A.closed q hcell

end FKIsingSquareFullCoordinateOneForm
end
end StatMech.Universality
