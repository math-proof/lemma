/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part4
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


theorem bool_xor_eq_xor_iff_eq_iff_eq (a b c d : Bool) :
    (a.xor c = b.xor d) <-> ((a = b) <-> (c = d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem typedSpinXor_cancel_right (sigma tau : V -> Bool) :
    typedSpinXor (typedSpinXor sigma tau) tau = sigma := by
  funext v
  simp [typedSpinXor]


end
end StatMech.FrontierA
