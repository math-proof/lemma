/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part3


namespace StatMech.FrontierA

open StatMech Lattice Sharpness


@[simp] theorem rectangularPrismConfigEquivSctBoxDobrushin_apply
    (n : Nat)
    (sigma : StatMech.Ising.RectangularPrismConfig
      (2 * n + 1) (2 * n + 1) n)
    (v : StatMech.Ising.RectangularPrismSite
      (2 * n + 1) (2 * n + 1) n) :
    rectangularPrismConfigEquivSctBoxDobrushin n sigma
        (rectangularPrismSiteEquivSctBoxDobrushin n v) = sigma v := by
  simp [rectangularPrismConfigEquivSctBoxDobrushin]

end StatMech.FrontierA
