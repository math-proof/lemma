/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part14
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def cubicalBelowSpin {a b c : Nat} (k : Fin (c + 1)) :
    CubicalDualVertex a b c -> Bool
  | none => false
  | some q => decide (q.z.val < k.val)

end
end StatMech.FrontierA
