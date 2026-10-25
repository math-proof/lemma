/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem quantumIsingBlockEquiv_apply (k L : Nat)
    (sigma : QuantumIsingChainConfig (k * L)) (b : Fin k) (i : Fin L) :
    quantumIsingBlockEquiv k L sigma b i = sigma (finProdFinEquiv (b, i)) := by
  rfl

@[simp] theorem cyclicSucc_finProd_castSucc
    (k L : Nat) (b : Fin (k + 1)) (i : Fin L) :
    quantumIsingCyclicSucc (finProdFinEquiv (b, i.castSucc)) =
      finProdFinEquiv (b, i.succ) := by
  apply Fin.ext
  change (i.val + (L + 1) * b.val + 1) % ((k + 1) * (L + 1)) =
    i.val + 1 + (L + 1) * b.val
  rw [Nat.mod_eq_of_lt]
  · ring
  · have hi : i.val + 1 ≤ L := by omega
    have hb0 : b.val + 1 ≤ k + 1 := by omega
    have hb := Nat.mul_le_mul_left (L + 1) hb0
    nlinarith

@[simp] theorem cyclicSucc_finProd_last_castSucc
    (k L : Nat) (b : Fin k) :
    quantumIsingCyclicSucc
        (finProdFinEquiv (b.castSucc, Fin.last L)) =
      finProdFinEquiv (b.succ, (0 : Fin (L + 1))) := by
  apply Fin.ext
  simp [quantumIsingCyclicSucc, finProdFinEquiv]
  have hb : b.val + 1 < k + 1 := by omega
  rw [Nat.mod_eq_of_lt]
  · ring
  · nlinarith [b.isLt]

@[simp] theorem cyclicSucc_finProd_last_last
    (k L : Nat) :
    quantumIsingCyclicSucc
        (finProdFinEquiv (Fin.last k, Fin.last L)) =
      finProdFinEquiv ((0 : Fin (k + 1)), (0 : Fin (L + 1))) := by
  apply Fin.ext
  change (L + (L + 1) * k + 1) % ((k + 1) * (L + 1)) = 0
  convert Nat.mod_self ((k + 1) * (L + 1)) using 2; ring

end StatMech.FrontierA
