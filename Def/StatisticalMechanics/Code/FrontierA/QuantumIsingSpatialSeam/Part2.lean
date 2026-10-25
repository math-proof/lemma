/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam
open scoped BigOperators


namespace StatMech.FrontierA

def quantumIsingSpatialPathEquiv (n L M : Nat) :
    (Fin n -> QuantumIsingChainConfig (L + M + 2)) ≃
      (Fin n -> QuantumIsingChainConfig (L + 1)) ×
        (Fin n -> QuantumIsingChainConfig (M + 1)) where
  toFun omega :=
    (fun k => quantumIsingLeftSpatialBlock L M (omega k),
      fun k => quantumIsingRightSpatialBlock L M (omega k))
  invFun omega := fun k => quantumIsingSpatialJoin L M (omega.1 k) (omega.2 k)
  left_inv omega := by
    funext k i
    obtain ⟨x, rfl⟩ := (quantumIsingSpatialSumEquiv L M).surjective i
    rcases x with i | j
    · simp only [quantumIsingSpatialJoin, Equiv.symm_apply_apply,
        Sum.elim_inl]
      unfold quantumIsingLeftSpatialBlock
      apply congrArg (omega k)
      apply Fin.ext
      simp [quantumIsingSpatialSumEquiv]
    · simp only [quantumIsingSpatialJoin, Equiv.symm_apply_apply,
        Sum.elim_inr]
      unfold quantumIsingRightSpatialBlock
      apply congrArg (omega k)
      apply Fin.ext
      simp [quantumIsingSpatialSumEquiv]
  right_inv omega := by
    apply Prod.ext
    · funext k
      exact quantumIsingLeftSpatialBlock_join L M (omega.1 k) (omega.2 k)
    · funext k
      exact quantumIsingRightSpatialBlock_join L M (omega.1 k) (omega.2 k)

end StatMech.FrontierA
