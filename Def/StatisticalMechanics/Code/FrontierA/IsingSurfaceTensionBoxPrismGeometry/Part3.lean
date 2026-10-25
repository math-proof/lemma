/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry.Part2


namespace StatMech.FrontierA

open StatMech Lattice Sharpness


def rectangularPrismConfigEquivSctBoxDobrushin (n : Nat) :
    StatMech.Ising.RectangularPrismConfig (2 * n + 1) (2 * n + 1) n ≃
      ({x : Site 3 // x ∈ box 3 n} -> Bool) :=
  Equiv.arrowCongr (rectangularPrismSiteEquivSctBoxDobrushin n)
    (Equiv.refl Bool)

end StatMech.FrontierA
