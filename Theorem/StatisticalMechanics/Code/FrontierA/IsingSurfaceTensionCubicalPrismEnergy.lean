/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy


namespace StatMech.FrontierA

open scoped BigOperators symmDiff

open Filter Topology

open StatMech StatMech.Ising

noncomputable section

@[simp] theorem oddCubicalCellEquivPrismSite_symm_apply
    (n : Nat) (v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n) :
    (oddCubicalCellEquivPrismSite n).symm v = ⟨v.x, v.y, v.z⟩ := rfl


end
end StatMech.FrontierA
