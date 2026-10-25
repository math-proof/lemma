/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def centralBottomZ (n : Nat) :
    Fin (centralSquareSide n + centralSquareSide n) :=
  ⟨0, by simp [centralSquareSide]⟩

end
end StatMech.FrontierA
