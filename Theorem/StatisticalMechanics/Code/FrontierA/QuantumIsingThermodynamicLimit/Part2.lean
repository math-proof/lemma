/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part2
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

theorem quantumIsingTwoBlockPeriodicInteraction_eq_open_seams
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) :
    quantumIsingTwoBlockPeriodicInteraction A B pair =
      quantumIsingTwoBlockOpenInteraction A B pair +
        quantumIsingSpinSign (pair.1 (Fin.last A)) *
          quantumIsingSpinSign (pair.1 0) +
        quantumIsingSpinSign (pair.2 (Fin.last B)) *
          quantumIsingSpinSign (pair.2 0) := by
  unfold quantumIsingTwoBlockPeriodicInteraction
  have hchain (L : Nat) (sigma : QuantumIsingChainConfig (L + 1)) :
      quantumIsingChainInteraction (L + 1) sigma =
        (∑ i : Fin L,
          quantumIsingSpinSign (sigma i.castSucc) *
            quantumIsingSpinSign (sigma i.succ)) +
          quantumIsingSpinSign (sigma (Fin.last L)) *
            quantumIsingSpinSign (sigma 0) := by
    unfold quantumIsingChainInteraction
    rw [Fin.sum_univ_castSucc]
    simp
  rw [hchain A pair.1, hchain B pair.2]
  unfold quantumIsingTwoBlockOpenInteraction
  ring

theorem quantumIsingTwoBlockLongInteraction_eq_open_seams
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) :
    quantumIsingTwoBlockLongInteraction A B pair =
      quantumIsingTwoBlockOpenInteraction A B pair +
        quantumIsingSpinSign (pair.1 (Fin.last A)) *
          quantumIsingSpinSign (pair.2 0) +
        quantumIsingSpinSign (pair.2 (Fin.last B)) *
          quantumIsingSpinSign (pair.1 0) := by
  unfold quantumIsingTwoBlockLongInteraction quantumIsingChainInteraction
  let flat := (quantumIsingSumBlockEquiv (A + 1) (B + 1)).symm pair
  calc
    (∑ q : Fin ((A + 1) + (B + 1)),
      quantumIsingSpinSign (flat q) *
        quantumIsingSpinSign (flat (quantumIsingCyclicSucc q))) =
      ∑ s : Fin (A + 1) ⊕ Fin (B + 1),
        quantumIsingSpinSign (flat (finSumFinEquiv s)) *
          quantumIsingSpinSign
            (flat (quantumIsingCyclicSucc (finSumFinEquiv s))) := by
      simpa using (Equiv.sum_comp finSumFinEquiv
        (fun q : Fin ((A + 1) + (B + 1)) =>
          quantumIsingSpinSign (flat q) *
            quantumIsingSpinSign (flat (quantumIsingCyclicSucc q)))).symm
    _ = (∑ i : Fin (A + 1),
          quantumIsingSpinSign (flat (finSumFinEquiv (Sum.inl i))) *
            quantumIsingSpinSign
              (flat (quantumIsingCyclicSucc
                (finSumFinEquiv (Sum.inl i))))) +
        ∑ j : Fin (B + 1),
          quantumIsingSpinSign (flat (finSumFinEquiv (Sum.inr j))) *
            quantumIsingSpinSign
              (flat (quantumIsingCyclicSucc
                (finSumFinEquiv (Sum.inr j)))) := by
      rw [Fintype.sum_sum_type]
    _ = _ := by
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp_rw [cyclicSucc_finSum_left_castSucc,
        cyclicSucc_finSum_left_last,
        cyclicSucc_finSum_right_castSucc,
        cyclicSucc_finSum_right_last]
      simp only [flat, quantumIsingSumBlockEquiv_symm_left,
        quantumIsingSumBlockEquiv_symm_right]
      simp only [quantumIsingTwoBlockOpenInteraction]
      ring

theorem abs_quantumIsingBond_le_one (s t : Bool) :
    |quantumIsingSpinSign s * quantumIsingSpinSign t| ≤ 1 := by
  rw [abs_mul, abs_quantumIsingSpinSign, abs_quantumIsingSpinSign]
  norm_num


theorem quantumIsingTwoBlockInteraction_sub_le
    (A B : Nat) (pair : QuantumIsingTwoBlockConfig (A + 1) (B + 1)) :
    |quantumIsingTwoBlockLongInteraction A B pair -
      quantumIsingTwoBlockPeriodicInteraction A B pair| ≤ 4 := by
  rw [quantumIsingTwoBlockLongInteraction_eq_open_seams,
    quantumIsingTwoBlockPeriodicInteraction_eq_open_seams]
  let a : Real := quantumIsingSpinSign (pair.1 (Fin.last A)) *
    quantumIsingSpinSign (pair.2 0)
  let b : Real := quantumIsingSpinSign (pair.2 (Fin.last B)) *
    quantumIsingSpinSign (pair.1 0)
  let c : Real := quantumIsingSpinSign (pair.1 (Fin.last A)) *
    quantumIsingSpinSign (pair.1 0)
  let d : Real := quantumIsingSpinSign (pair.2 (Fin.last B)) *
    quantumIsingSpinSign (pair.2 0)
  change |quantumIsingTwoBlockOpenInteraction A B pair + a + b -
    (quantumIsingTwoBlockOpenInteraction A B pair + c + d)| ≤ 4
  rw [show quantumIsingTwoBlockOpenInteraction A B pair + a + b -
      (quantumIsingTwoBlockOpenInteraction A B pair + c + d) =
      a + b - c - d by ring]
  calc
    |a + b - c - d| ≤ |a + b - c| + |d| := by
      simpa [sub_eq_add_neg] using abs_add_le (a + b - c) (-d)
    _ ≤ (|a + b| + |c|) + |d| := by
      gcongr
      simpa [sub_eq_add_neg] using abs_add_le (a + b) (-c)
    _ ≤ ((|a| + |b|) + |c|) + |d| := by
      gcongr
      exact abs_add_le a b
    _ = 4 := by
      dsimp [a, b, c, d]
      simp [abs_quantumIsingSpinSign]
      norm_num


end StatMech.FrontierA
