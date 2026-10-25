/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal


namespace StatMech.FrontierA

@[simp] theorem quantumIsingSpinSign_false :
    quantumIsingSpinSign false = -1 := rfl

@[simp] theorem quantumIsingSpinSign_true :
    quantumIsingSpinSign true = 1 := rfl

theorem quantumIsingSpinSign_mul_self (s : Bool) :
    quantumIsingSpinSign s * quantumIsingSpinSign s = 1 := by
  cases s <;> norm_num [quantumIsingSpinSign]

theorem quantumIsingSpinSign_mul_eq_neg_one_of_ne
    {s t : Bool} (hst : s ≠ t) :
    quantumIsingSpinSign s * quantumIsingSpinSign t = -1 := by
  cases s <;> cases t <;> simp_all [quantumIsingSpinSign]


end StatMech.FrontierA
