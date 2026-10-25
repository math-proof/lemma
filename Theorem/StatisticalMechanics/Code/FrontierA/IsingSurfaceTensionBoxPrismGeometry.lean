/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetGauge
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismGeometry


namespace StatMech.FrontierA

open StatMech Lattice Sharpness


@[simp] theorem finOddEquivCenteredInt_apply_val
    (n : Nat) (i : Fin (2 * n + 1)) :
    (finOddEquivCenteredInt n i).1 = (i.val : Int) - n := rfl


end StatMech.FrontierA
