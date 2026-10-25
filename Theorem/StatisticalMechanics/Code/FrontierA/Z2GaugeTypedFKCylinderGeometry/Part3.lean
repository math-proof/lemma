/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem centralLowerZ_val {n : Nat}
    (z : Fin (centralSquareSide n)) :
    (centralLowerZ z).val = z.val := rfl

end
end StatMech.FrontierA
