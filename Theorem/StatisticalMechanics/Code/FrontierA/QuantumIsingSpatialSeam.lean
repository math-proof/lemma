/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem quantumIsingLeftSpatialBlock_join
    (L M : Nat) (sigma : QuantumIsingChainConfig (L + 1))
    (tau : QuantumIsingChainConfig (M + 1)) :
    quantumIsingLeftSpatialBlock L M
        (quantumIsingSpatialJoin L M sigma tau) = sigma := by
  funext i
  unfold quantumIsingLeftSpatialBlock quantumIsingSpatialJoin
  rw [show (⟨i.val, by omega⟩ : Fin (L + M + 2)) =
      quantumIsingSpatialSumEquiv L M (Sum.inl i) by
    apply Fin.ext
    simp [quantumIsingSpatialSumEquiv]]
  simp

@[simp] theorem quantumIsingRightSpatialBlock_join
    (L M : Nat) (sigma : QuantumIsingChainConfig (L + 1))
    (tau : QuantumIsingChainConfig (M + 1)) :
    quantumIsingRightSpatialBlock L M
        (quantumIsingSpatialJoin L M sigma tau) = tau := by
  funext i
  unfold quantumIsingRightSpatialBlock quantumIsingSpatialJoin
  rw [show (⟨L + 1 + i.val, by omega⟩ : Fin (L + M + 2)) =
      quantumIsingSpatialSumEquiv L M (Sum.inr i) by
    apply Fin.ext
    simp [quantumIsingSpatialSumEquiv]]
  simp


end StatMech.FrontierA
