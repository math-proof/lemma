/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
open scoped BigOperators


namespace StatMech.FrontierA

@[simp] theorem quantumIsingSpaceTimeBlockSwapEquiv_apply
    (n k L : Nat) (omega : QuantumIsingSpaceTimeBlockConfig n k L)
    (b : Fin k) (t : Fin n) :
    quantumIsingSpaceTimeBlockSwapEquiv n k L omega b t = omega t b := rfl

@[simp] theorem quantumIsingSpaceTimeBlockSwapEquiv_symm_apply
    (n k L : Nat) (omega : Fin k -> Fin n -> QuantumIsingChainConfig L)
    (t : Fin n) (b : Fin k) :
    (quantumIsingSpaceTimeBlockSwapEquiv n k L).symm omega t b = omega b t := rfl


theorem quantumIsingBlockPeriodicCylinderWeight_sum
    (beta h : Real) (n k L : Nat) :
    (∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
      quantumIsingBlockPeriodicCylinderWeight beta h n k L omega) =
      quantumIsingClassicalCylinderPartition beta h n (L + 1) ^ (k + 1) := by
  let e := quantumIsingSpaceTimeBlockSwapEquiv n (k + 1) (L + 1)
  calc
    (∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
      quantumIsingBlockPeriodicCylinderWeight beta h n k L omega) =
      ∑ blocks : Fin (k + 1) -> Fin n -> QuantumIsingChainConfig (L + 1),
        quantumIsingBlockPeriodicCylinderWeight beta h n k L (e.symm blocks) := by
      simpa using (Equiv.sum_comp e
        (fun blocks : Fin (k + 1) -> Fin n -> QuantumIsingChainConfig (L + 1) =>
          quantumIsingBlockPeriodicCylinderWeight beta h n k L (e.symm blocks)))
    _ = ∑ blocks : Fin (k + 1) -> Fin n -> QuantumIsingChainConfig (L + 1),
        ∏ b : Fin (k + 1),
          quantumIsingClassicalCylinderWeight beta h n (L + 1) (blocks b) := by
      apply Finset.sum_congr rfl
      intro blocks _
      rw [quantumIsingBlockPeriodicCylinderWeight_eq_prod]
      rfl
    _ = (∑ cylinder : Fin n -> QuantumIsingChainConfig (L + 1),
        quantumIsingClassicalCylinderWeight beta h n (L + 1) cylinder) ^
          (k + 1) := by
      rw [Finset.sum_pow'
        (Finset.univ : Finset (Fin n -> QuantumIsingChainConfig (L + 1)))
        (quantumIsingClassicalCylinderWeight beta h n (L + 1)) (k + 1)]
      simp
    _ = quantumIsingClassicalCylinderPartition beta h n (L + 1) ^ (k + 1) := by
      rfl

theorem quantumIsingClassicalCylinderPartition_block_sum
    (beta h : Real) (n k L : Nat) :
    quantumIsingClassicalCylinderPartition beta h n ((k + 1) * (L + 1)) =
      ∑ omega : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
        quantumIsingBlockLongCylinderWeight beta h n k L omega := by
  unfold quantumIsingClassicalCylinderPartition
  let e := quantumIsingSpaceTimeBlockEquiv n (k + 1) (L + 1)
  calc
    (∑ omega : Fin n -> QuantumIsingChainConfig ((k + 1) * (L + 1)),
      quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1)) omega) =
      ∑ blocks : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
        quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1))
          (e.symm blocks) := by
      simpa using (Equiv.sum_comp e
        (fun blocks : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1) =>
          quantumIsingClassicalCylinderWeight beta h n ((k + 1) * (L + 1))
            (e.symm blocks)))
    _ = ∑ blocks : QuantumIsingSpaceTimeBlockConfig n (k + 1) (L + 1),
        quantumIsingBlockLongCylinderWeight beta h n k L blocks := by
      apply Finset.sum_congr rfl
      intro blocks _
      exact quantumIsingClassicalCylinderWeight_blockEquiv beta h n k L blocks


theorem quantumIsingClassicalCylinderPartition_block_upper
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta) :
    quantumIsingClassicalCylinderPartition beta h (n + 1)
        ((k + 1) * (L + 1)) ≤
      quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) *
        Real.exp (beta * (k + 1) / 2) := by
  rw [quantumIsingClassicalCylinderPartition_block_sum]
  calc
    (∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
      quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega) ≤
      ∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
        Real.exp (beta * (k + 1) / 2) *
          quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega := by
      apply Finset.sum_le_sum
      intro omega _
      exact quantumIsingBlockLongCylinderWeight_le beta h n k L hbeta omega
    _ = Real.exp (beta * (k + 1) / 2) *
        (∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
          quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega) := by
      rw [Finset.mul_sum]
    _ = Real.exp (beta * (k + 1) / 2) *
        quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) := by
      rw [quantumIsingBlockPeriodicCylinderWeight_sum]
    _ = _ := by ring


theorem quantumIsingClassicalCylinderPartition_block_lower
    (beta h : Real) (n k L : Nat) (hbeta : 0 ≤ beta) :
    quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) *
        Real.exp (-beta * (k + 1) / 2) ≤
      quantumIsingClassicalCylinderPartition beta h (n + 1)
        ((k + 1) * (L + 1)) := by
  have hsum :
      quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) ≤
        Real.exp (beta * (k + 1) / 2) *
          quantumIsingClassicalCylinderPartition beta h (n + 1)
            ((k + 1) * (L + 1)) := by
    rw [quantumIsingClassicalCylinderPartition_block_sum,
      ← quantumIsingBlockPeriodicCylinderWeight_sum]
    calc
      (∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
        quantumIsingBlockPeriodicCylinderWeight beta h (n + 1) k L omega) ≤
        ∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
          Real.exp (beta * (k + 1) / 2) *
            quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
        apply Finset.sum_le_sum
        intro omega _
        exact quantumIsingBlockPeriodicCylinderWeight_le beta h n k L hbeta omega
      _ = Real.exp (beta * (k + 1) / 2) *
          ∑ omega : QuantumIsingSpaceTimeBlockConfig (n + 1) (k + 1) (L + 1),
            quantumIsingBlockLongCylinderWeight beta h (n + 1) k L omega := by
        rw [Finset.mul_sum]
  calc
    quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) * Real.exp (-beta * (k + 1) / 2) =
      Real.exp (-beta * (k + 1) / 2) *
        quantumIsingClassicalCylinderPartition beta h (n + 1) (L + 1) ^
          (k + 1) := by ring
    _ ≤ Real.exp (-beta * (k + 1) / 2) *
        (Real.exp (beta * (k + 1) / 2) *
          quantumIsingClassicalCylinderPartition beta h (n + 1)
            ((k + 1) * (L + 1))) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = quantumIsingClassicalCylinderPartition beta h (n + 1)
        ((k + 1) * (L + 1)) := by
      rw [← mul_assoc, ← Real.exp_add,
        show -beta * (k + 1 : Real) / 2 + beta * (k + 1 : Real) / 2 = 0 by ring,
        Real.exp_zero, one_mul]

end StatMech.FrontierA
