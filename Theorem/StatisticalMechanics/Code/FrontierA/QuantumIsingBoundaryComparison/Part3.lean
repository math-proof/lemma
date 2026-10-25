/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part3
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingBlockLongInteraction_eq_open_add
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    quantumIsingBlockLongInteraction k L sigma =
      quantumIsingBlockOpenInteraction k L sigma +
        quantumIsingBlockLongSeamInteraction k L sigma := by
  unfold quantumIsingBlockLongInteraction quantumIsingChainInteraction
  let flat := (quantumIsingBlockEquiv (k + 1) (L + 1)).symm sigma
  calc
    (∑ j : Fin ((k + 1) * (L + 1)),
        quantumIsingSpinSign (flat j) *
          quantumIsingSpinSign (flat (quantumIsingCyclicSucc j))) =
      ∑ p : Fin (k + 1) × Fin (L + 1),
        quantumIsingSpinSign (flat (finProdFinEquiv p)) *
          quantumIsingSpinSign
            (flat (quantumIsingCyclicSucc (finProdFinEquiv p))) := by
      exact (Equiv.sum_comp finProdFinEquiv _).symm
    _ = ∑ b : Fin (k + 1), ∑ i : Fin (L + 1),
        quantumIsingSpinSign (flat (finProdFinEquiv (b, i))) *
          quantumIsingSpinSign
            (flat (quantumIsingCyclicSucc (finProdFinEquiv (b, i)))) := by
      rw [Fintype.sum_prod_type]
    _ = quantumIsingBlockOpenInteraction k L sigma +
        quantumIsingBlockLongSeamInteraction k L sigma := by
      rw [Fin.sum_univ_castSucc]
      have hblocks :
          (∑ b : Fin k, ∑ i : Fin (L + 1),
            quantumIsingSpinSign (flat (finProdFinEquiv (b.castSucc, i))) *
              quantumIsingSpinSign
                (flat (quantumIsingCyclicSucc
                  (finProdFinEquiv (b.castSucc, i))))) =
            ∑ b : Fin k,
              ((∑ i : Fin L,
                quantumIsingSpinSign (sigma b.castSucc i.castSucc) *
                  quantumIsingSpinSign (sigma b.castSucc i.succ)) +
                quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
                  quantumIsingSpinSign (sigma b.succ 0)) := by
        apply Finset.sum_congr rfl
        intro b _
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [cyclicSucc_finProd_castSucc]
          simp [flat]
        · rw [cyclicSucc_finProd_last_castSucc]
          simp [flat]
      have hlast :
          (∑ i : Fin (L + 1),
            quantumIsingSpinSign (flat (finProdFinEquiv (Fin.last k, i))) *
              quantumIsingSpinSign
                (flat (quantumIsingCyclicSucc
                  (finProdFinEquiv (Fin.last k, i))))) =
            (∑ i : Fin L,
              quantumIsingSpinSign (sigma (Fin.last k) i.castSucc) *
                quantumIsingSpinSign (sigma (Fin.last k) i.succ)) +
              quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
                quantumIsingSpinSign (sigma 0 0) := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro i _
          rw [cyclicSucc_finProd_castSucc]
          simp [flat]
        · rw [cyclicSucc_finProd_last_last]
          simp [flat]
      rw [hblocks, hlast]
      simp only [quantumIsingBlockOpenInteraction,
        quantumIsingBlockLongSeamInteraction]
      rw [Fin.sum_univ_castSucc, Finset.sum_add_distrib]
      ring

@[simp] theorem abs_quantumIsingSpinSign (s : Bool) :
    |quantumIsingSpinSign s| = 1 := by
  cases s <;> norm_num [quantumIsingSpinSign]

theorem abs_quantumIsingBond (s t : Bool) :
    |quantumIsingSpinSign s * quantumIsingSpinSign t| = 1 := by
  rw [abs_mul, abs_quantumIsingSpinSign, abs_quantumIsingSpinSign, mul_one]

theorem abs_blockPeriodicSeam_le
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    |∑ b : Fin (k + 1),
      quantumIsingSpinSign (sigma b (Fin.last L)) *
        quantumIsingSpinSign (sigma b 0)| ≤ (k + 1 : Real) := by
  calc
    |_|
        ≤ ∑ b : Fin (k + 1),
            |quantumIsingSpinSign (sigma b (Fin.last L)) *
              quantumIsingSpinSign (sigma b 0)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _b : Fin (k + 1), (1 : Real) := by
      apply Finset.sum_congr rfl
      intro b _
      exact abs_quantumIsingBond _ _
    _ = (k + 1 : Real) := by simp

theorem abs_blockLongSeam_le
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    |quantumIsingBlockLongSeamInteraction k L sigma| ≤ (k + 1 : Real) := by
  unfold quantumIsingBlockLongSeamInteraction
  calc
    |(∑ b : Fin k,
        quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
          quantumIsingSpinSign (sigma b.succ 0)) +
        quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
          quantumIsingSpinSign (sigma 0 0)| ≤
      |∑ b : Fin k,
        quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
          quantumIsingSpinSign (sigma b.succ 0)| +
        |quantumIsingSpinSign (sigma (Fin.last k) (Fin.last L)) *
          quantumIsingSpinSign (sigma 0 0)| := abs_add_le _ _
    _ ≤ (∑ b : Fin k,
        |quantumIsingSpinSign (sigma b.castSucc (Fin.last L)) *
          quantumIsingSpinSign (sigma b.succ 0)|) + 1 := by
      gcongr
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact le_of_eq (abs_quantumIsingBond _ _)
    _ = (k + 1 : Real) := by
      simp


theorem quantumIsingBlockInteraction_sub_le
    (k L : Nat) (sigma : QuantumIsingBlockConfig (k + 1) (L + 1)) :
    |quantumIsingBlockLongInteraction k L sigma -
      quantumIsingBlockPeriodicInteraction k L sigma| ≤
        2 * (k + 1 : Real) := by
  rw [quantumIsingBlockLongInteraction_eq_open_add,
    quantumIsingBlockPeriodicInteraction_eq_open_add]
  have hlong := abs_blockLongSeam_le k L sigma
  have hperiodic := abs_blockPeriodicSeam_le k L sigma
  calc
    |quantumIsingBlockOpenInteraction k L sigma +
          quantumIsingBlockLongSeamInteraction k L sigma -
        (quantumIsingBlockOpenInteraction k L sigma +
          ∑ b : Fin (k + 1),
            quantumIsingSpinSign (sigma b (Fin.last L)) *
              quantumIsingSpinSign (sigma b 0))| =
      |quantumIsingBlockLongSeamInteraction k L sigma -
        ∑ b : Fin (k + 1),
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0)| := by ring_nf
    _ ≤ |quantumIsingBlockLongSeamInteraction k L sigma| +
        |∑ b : Fin (k + 1),
          quantumIsingSpinSign (sigma b (Fin.last L)) *
            quantumIsingSpinSign (sigma b 0)| := abs_sub _ _
    _ ≤ (k + 1 : Real) + (k + 1 : Real) := add_le_add hlong hperiodic
    _ = 2 * (k + 1 : Real) := by ring

end StatMech.FrontierA
