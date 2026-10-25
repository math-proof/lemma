/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

@[simp] theorem quantumIsingSumBlockEquiv_apply_left
    (A B : Nat) (sigma : QuantumIsingChainConfig (A + B)) (i : Fin A) :
    (quantumIsingSumBlockEquiv A B sigma).1 i =
      sigma (finSumFinEquiv (Sum.inl i)) := rfl

@[simp] theorem quantumIsingSumBlockEquiv_apply_right
    (A B : Nat) (sigma : QuantumIsingChainConfig (A + B)) (j : Fin B) :
    (quantumIsingSumBlockEquiv A B sigma).2 j =
      sigma (finSumFinEquiv (Sum.inr j)) := rfl

@[simp] theorem quantumIsingSumBlockEquiv_symm_left
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig A B) (i : Fin A) :
    (quantumIsingSumBlockEquiv A B).symm pair
        (finSumFinEquiv (Sum.inl i)) = pair.1 i := by
  simp [quantumIsingSumBlockEquiv]

@[simp] theorem quantumIsingSumBlockEquiv_symm_right
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig A B) (j : Fin B) :
    (quantumIsingSumBlockEquiv A B).symm pair
        (finSumFinEquiv (Sum.inr j)) = pair.2 j := by
  simp [quantumIsingSumBlockEquiv]

@[simp] theorem cyclicSucc_finSum_left_castSucc
    (A B : Nat) (i : Fin A) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inl i.castSucc) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inl i.succ) := by
  apply Fin.ext
  change (i.val + 1) % ((A + 1) + (B + 1)) = i.val + 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem cyclicSucc_finSum_left_last
    (A B : Nat) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inl (Fin.last A)) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inr (0 : Fin (B + 1))) := by
  apply Fin.ext
  change (A + 1) % ((A + 1) + (B + 1)) = A + 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem cyclicSucc_finSum_right_castSucc
    (A B : Nat) (j : Fin B) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inr j.castSucc) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inr j.succ) := by
  apply Fin.ext
  change ((A + 1) + j.val + 1) % ((A + 1) + (B + 1)) =
    (A + 1) + (j.val + 1)
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

@[simp] theorem cyclicSucc_finSum_right_last
    (A B : Nat) :
    quantumIsingCyclicSucc
        (finSumFinEquiv (Sum.inr (Fin.last B)) : Fin ((A + 1) + (B + 1))) =
      finSumFinEquiv (Sum.inl (0 : Fin (A + 1))) := by
  apply Fin.ext
  change ((A + 1) + B + 1) % ((A + 1) + (B + 1)) = 0
  simp [Nat.add_assoc]

end StatMech.FrontierA
