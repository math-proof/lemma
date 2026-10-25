/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part2
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem quantumIsingBlockEquiv_symm_apply (k L : Nat)
    (sigma : QuantumIsingBlockConfig k L) (b : Fin k) (i : Fin L) :
    (quantumIsingBlockEquiv k L).symm sigma (finProdFinEquiv (b, i)) =
      sigma b i := by
  change sigma (finProdFinEquiv.symm (finProdFinEquiv (b, i))).1
    (finProdFinEquiv.symm (finProdFinEquiv (b, i))).2 = sigma b i
  rw [Equiv.symm_apply_apply]

@[simp] theorem quantumIsingCyclicSucc_castSucc
    (L : Nat) (i : Fin L) :
    quantumIsingCyclicSucc i.castSucc = i.succ := by
  apply Fin.ext
  change (i.val + 1) % (L + 1) = i.val + 1
  rw [Nat.mod_eq_of_lt]
  omega

@[simp] theorem quantumIsingCyclicSucc_last (L : Nat) :
    quantumIsingCyclicSucc (Fin.last L) = (0 : Fin (L + 1)) := by
  apply Fin.ext
  change (L + 1) % (L + 1) = 0
  exact Nat.mod_self _

theorem quantumIsingBlockPeriodicInteraction_eq_open_add
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    quantumIsingBlockPeriodicInteraction k L sigma =
      quantumIsingBlockOpenInteraction k L sigma +
        ∑ b : Fin (k + 1),
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0) := by 
  unfold quantumIsingBlockPeriodicInteraction quantumIsingBlockOpenInteraction
  have hblock (b : Fin (k + 1)) :
      quantumIsingChainInteraction (L + 1) (sigma b) =
        (∑ i : Fin L,
          quantumIsingSpinSign (sigma b i.castSucc) *
            quantumIsingSpinSign (sigma b i.succ)) +
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0) := by
    unfold quantumIsingChainInteraction
    rw [Fin.sum_univ_castSucc]
    simp
  simp_rw [hblock]
  rw [Finset.sum_add_distrib]

end StatMech.FrontierA
