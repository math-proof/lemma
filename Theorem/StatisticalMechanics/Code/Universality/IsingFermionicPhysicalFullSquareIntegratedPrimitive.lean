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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareIntegratedPrimitive


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

namespace FKIsingSquareFullIntegratedPrimitive

theorem shiftedCoordinate_coordinateIndex
    (n : Nat) (q : Int × Int) (hq : FKIsingSquareFullDiamond n q) :
    shiftedCoordinate n (coordinateIndex n q).1 (coordinateIndex n q).2 = q := by
  have hq0 : -(2 * (n : Int)) ≤ q.1 := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  have hq1 : -(2 * (n : Int)) ≤ q.2 := by
    rcases hq with ⟨h0, h1, h2, h3⟩
    omega
  apply Prod.ext <;>
    simp [shiftedCoordinate, coordinateIndex] <;>
    omega

theorem diamondCell_of_row_interval
    (n i j k : Nat)
    (h0 : FKIsingSquareFullDiamond n (shiftedCoordinate n i j))
    (h1 : FKIsingSquareFullDiamond n (shiftedCoordinate n i (j + 1)))
    (hk : (2 * n ≤ k ∧ k < i) ∨ (i ≤ k ∧ k < 2 * n)) :
    FKIsingSquareFullDiamondCell n (shiftedCoordinate n k j) := by
  rcases h0 with ⟨h00, h01, h02, h03⟩
  rcases h1 with ⟨h10, h11, h12, h13⟩
  simp [shiftedCoordinate] at h00 h01 h02 h03 h10 h11 h12 h13
  simp only [FKIsingSquareFullDiamondCell, FKIsingSquareFullDiamond,
    shiftedCoordinate]
  rcases hk with hk | hk
  all_goals repeat' apply And.intro
  all_goals omega

end FKIsingSquareFullIntegratedPrimitive
end
end StatMech.Universality
