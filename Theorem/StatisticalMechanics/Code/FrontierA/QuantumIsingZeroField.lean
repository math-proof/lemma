/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFreeEnergy
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingZeroField
open Filter Matrix
open scoped Topology BigOperators


namespace StatMech.FrontierA

@[simp] theorem transferSpin_quantumIsingBoolTransferEquiv (b : Bool) :
    FrontierC.transferSpin (quantumIsingBoolTransferEquiv b) =
      quantumIsingSpinSign b := by
  cases b <;> simp [quantumIsingBoolTransferEquiv]


end StatMech.FrontierA
