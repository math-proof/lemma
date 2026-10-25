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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem primitiveNat_horizontal_increment
    (n : Nat) (hn : 0 < n) (i j : Nat) :
    primitiveNat n hn (i + 1) j - primitiveNat n hn i j =
      horizontalNat n hn i j := by
  exact isingCenteredPrimitive_horizontal_increment
    (horizontalNat n hn) (verticalNat n hn) (2 * n) i j

theorem primitiveNat_vertical_increment
    (n : Nat) (hn : 0 < n) (i j : Nat)
    (h0 : FKIsingSquareFullDiamond n (shiftedCoordinate n i j))
    (h1 : FKIsingSquareFullDiamond n (shiftedCoordinate n i (j + 1))) :
    primitiveNat n hn i (j + 1) - primitiveNat n hn i j =
      verticalNat n hn i j := by
  apply isingCenteredPrimitive_vertical_increment
  intro k hk
  have hcell := diamondCell_of_row_interval n i j k h0 h1 hk
  have hx : shiftedCoordinate n (k + 1) j =
      ((shiftedCoordinate n k j).1 + 1, (shiftedCoordinate n k j).2) := by
    apply Prod.ext <;> simp [shiftedCoordinate] <;> omega
  have hy : shiftedCoordinate n k (j + 1) =
      ((shiftedCoordinate n k j).1, (shiftedCoordinate n k j).2 + 1) := by
    apply Prod.ext <;> simp [shiftedCoordinate] <;> omega
  dsimp [verticalNat, horizontalNat]
  rw [hx, hy]
  exact fkIsingSquareFull_increment_closed n hn (shiftedCoordinate n k j) hcell

theorem coordinateIndex_east
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    coordinateIndex n (q.1 + 1, q.2) =
      ((coordinateIndex n q).1 + 1, (coordinateIndex n q).2) := by
  have hq0 : 0 ≤ q.1 + 2 * (n : Int) := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  apply Prod.ext <;> simp [coordinateIndex] <;> omega

theorem coordinateIndex_north
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    coordinateIndex n (q.1, q.2 + 1) =
      ((coordinateIndex n q).1, (coordinateIndex n q).2 + 1) := by
  have hq1 : 0 ≤ q.2 + 2 * (n : Int) := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  apply Prod.ext <;> simp [coordinateIndex] <;> omega

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
