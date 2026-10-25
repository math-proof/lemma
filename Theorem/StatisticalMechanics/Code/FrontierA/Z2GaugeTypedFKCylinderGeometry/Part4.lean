/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part4
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

@[simp] theorem centralBottomZ_val (n : Nat) :
    (centralBottomZ n).val = 0 := rfl

@[simp] theorem finForward_eq_none_iff' {m : Nat} (f : Fin (m + 1)) :
    finForward f = none ↔ f = Fin.last m := by
  refine Fin.lastCases ?_ (fun z => ?_) f
  · simp [finForward]
  · simp [finForward]

end
end StatMech.FrontierA
