/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part2


namespace StatMech.FrontierA

open StatMech Lattice Sharpness


@[simp] theorem rectangularPrismSiteEquivSctBoxDobrushin_apply_zero
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1 0 =
      (v.x.val : Int) - n := by
  simp [rectangularPrismSiteEquivSctBoxDobrushin, reflectThirdBoxEquiv,
    rectangularPrismSiteEquivSctBox, rectangularPrismSiteCentered]

@[simp] theorem rectangularPrismSiteEquivSctBoxDobrushin_apply_one
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1 1 =
      (v.y.val : Int) - n := by
  simp [rectangularPrismSiteEquivSctBoxDobrushin, reflectThirdBoxEquiv,
    rectangularPrismSiteEquivSctBox, rectangularPrismSiteCentered]

@[simp] theorem rectangularPrismSiteEquivSctBoxDobrushin_apply_two
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (rectangularPrismSiteEquivSctBoxDobrushin n v).1 2 =
      (n : Int) - v.z.val := by
  simp [rectangularPrismSiteEquivSctBoxDobrushin, reflectThirdBoxEquiv,
    rectangularPrismSiteEquivSctBox, rectangularPrismSiteCentered]


theorem interfaceField_rectangularPrismSiteEquivSctBoxDobrushin
    (n : Nat)
    (v : StatMech.Ising.RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    StatMech.Ising.interfaceField (⟨2, by omega⟩ : Fin 3)
        (rectangularPrismSiteEquivSctBoxDobrushin n v).1 =
      decide (v.z.val <= n) := by
  change decide (0 <=
      (rectangularPrismSiteEquivSctBoxDobrushin n v).1 2) = _
  rw [rectangularPrismSiteEquivSctBoxDobrushin_apply_two]
  simp only [sub_nonneg]
  norm_cast


end StatMech.FrontierA
