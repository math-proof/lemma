/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTwoPointComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4RadialDecay.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTwoPointComparison
open MeasureTheory SimpleGraph
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

noncomputable section

theorem fkRectHorizontalCylinder_displacement_add_correction
    (dx : Int) (height : Nat) :
    fkRectHorizontalCylinderLiftedDisplacement dx height +
        fkRectHorizontalCylinderCorrection dx =
      fkRectHorizontalCylinderVerticalDisplacement height := by
  funext i
  fin_cases i <;>
    simp [fkRectHorizontalCylinderLiftedDisplacement,
      fkRectHorizontalCylinderCorrection,
      fkRectHorizontalCylinderVerticalDisplacement]


theorem fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical
    {q : Real} (hq : 4 < q) (dx : Int) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderLiftedDisplacement dx height) *
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderCorrection dx) <=
      fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderVerticalDisplacement height) := by
  have h := fkQgt4CriticalFreeTwoPoint_add_supermultiplicative hq
    (fkRectHorizontalCylinderLiftedDisplacement dx height)
    (fkRectHorizontalCylinderCorrection dx)
  rwa [fkRectHorizontalCylinder_displacement_add_correction] at h


theorem fkQgt4CriticalFreeTwoPoint_horizontalCylinder_le_vertical_div
    {q : Real} (hq : 4 < q) (dx : Int) (height : Nat) :
    fkQgt4CriticalFreeTwoPoint hq
        (fkRectHorizontalCylinderLiftedDisplacement dx height) <=
      fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderVerticalDisplacement height) /
        fkQgt4CriticalFreeTwoPoint hq
          (fkRectHorizontalCylinderCorrection dx) := by
  rw [le_div_iff₀ (fkQgt4CriticalFreeTwoPoint_pos hq
    (fkRectHorizontalCylinderCorrection dx))]
  exact
    fkQgt4CriticalFreeTwoPoint_horizontalCylinder_mul_correction_le_vertical
      hq dx height


end
end StatMech.FrontierD
