/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingZeroField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingFreeEnergy
open Filter Matrix
open scoped Topology BigOperators


namespace StatMech.FrontierA

def quantumIsingBoolTransferEquiv : Bool ≃ Fin 2 where
  toFun b := if b then 0 else 1
  invFun s := s = 0
  left_inv b := by cases b <;> simp
  right_inv s := by fin_cases s <;> simp

end StatMech.FrontierA
