/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingThermodynamicLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingBoundaryComparison.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingThermodynamicLimit.Part5
open scoped BigOperators
open Filter


namespace StatMech.FrontierA

theorem quantumIsingTwoBlockPeriodicCylinderWeight_sum
    (beta h : Real) (n A B : Nat) :
    (∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
      quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega) =
      quantumIsingClassicalCylinderPartition beta h n (A + 1) *
        quantumIsingClassicalCylinderPartition beta h n (B + 1) := by
  let e := quantumIsingSpaceTimeTwoBlockSplitEquiv n (A + 1) (B + 1)
  calc
    (∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
      quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B omega) =
      ∑ pair : (Fin n -> QuantumIsingChainConfig (A + 1)) ×
          (Fin n -> QuantumIsingChainConfig (B + 1)),
        quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B (e.symm pair) := by
      simpa using (Equiv.sum_comp e
        (fun pair : (Fin n -> QuantumIsingChainConfig (A + 1)) ×
            (Fin n -> QuantumIsingChainConfig (B + 1)) =>
          quantumIsingTwoBlockPeriodicCylinderWeight beta h n A B (e.symm pair)))
    _ = ∑ pair : (Fin n -> QuantumIsingChainConfig (A + 1)) ×
          (Fin n -> QuantumIsingChainConfig (B + 1)),
        quantumIsingClassicalCylinderWeight beta h n (A + 1) pair.1 *
          quantumIsingClassicalCylinderWeight beta h n (B + 1) pair.2 := by
      apply Finset.sum_congr rfl
      intro pair _
      rw [quantumIsingTwoBlockPeriodicCylinderWeight_eq_mul]
      rfl
    _ = (∑ left : Fin n -> QuantumIsingChainConfig (A + 1),
          quantumIsingClassicalCylinderWeight beta h n (A + 1) left) *
        ∑ right : Fin n -> QuantumIsingChainConfig (B + 1),
          quantumIsingClassicalCylinderWeight beta h n (B + 1) right := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = _ := by rfl

theorem quantumIsingClassicalCylinderPartition_twoBlock_sum
    (beta h : Real) (n A B : Nat) :
    quantumIsingClassicalCylinderPartition beta h n ((A + 1) + (B + 1)) =
      ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
        quantumIsingTwoBlockLongCylinderWeight beta h n A B omega := by
  unfold quantumIsingClassicalCylinderPartition
  let e := quantumIsingSpaceTimeSumBlockEquiv n (A + 1) (B + 1)
  calc
    (∑ omega : Fin n -> QuantumIsingChainConfig ((A + 1) + (B + 1)),
      quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1)) omega) =
      ∑ pair : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1),
        quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1))
          (e.symm pair) := by
      simpa using (Equiv.sum_comp e
        (fun pair : QuantumIsingSpaceTimeTwoBlockConfig n (A + 1) (B + 1) =>
          quantumIsingClassicalCylinderWeight beta h n ((A + 1) + (B + 1))
            (e.symm pair)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro pair _
      exact quantumIsingClassicalCylinderWeight_sumBlockEquiv beta h n A B pair


theorem quantumIsingClassicalCylinderPartition_add_upper
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta) :
    quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) ≤
      Real.exp beta *
        (quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)) := by
  rw [quantumIsingClassicalCylinderPartition_twoBlock_sum]
  calc
    _ ≤ ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1),
        Real.exp beta * quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
      apply Finset.sum_le_sum
      intro omega _
      exact quantumIsingTwoBlockLongCylinderWeight_le beta h n A B hbeta omega
    _ = Real.exp beta *
        ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1),
          quantumIsingTwoBlockPeriodicCylinderWeight beta h (n + 1) A B omega := by
      rw [Finset.mul_sum]
    _ = _ := by rw [quantumIsingTwoBlockPeriodicCylinderWeight_sum]


theorem quantumIsingClassicalCylinderPartition_add_lower
    (beta h : Real) (n A B : Nat) (hbeta : 0 ≤ beta) :
    Real.exp (-beta) *
        (quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1)) ≤
      quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) := by
  have hsum :
      quantumIsingClassicalCylinderPartition beta h (n + 1) (A + 1) *
          quantumIsingClassicalCylinderPartition beta h (n + 1) (B + 1) ≤
        Real.exp beta *
          quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1)) := by
    rw [quantumIsingClassicalCylinderPartition_twoBlock_sum,
      ← quantumIsingTwoBlockPeriodicCylinderWeight_sum]
    calc
      _ ≤ ∑ omega : QuantumIsingSpaceTimeTwoBlockConfig (n + 1) (A + 1) (B + 1),
          Real.exp beta * quantumIsingTwoBlockLongCylinderWeight beta h (n + 1) A B omega := by
        apply Finset.sum_le_sum
        intro omega _
        exact quantumIsingTwoBlockPeriodicCylinderWeight_le beta h n A B hbeta omega
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ Real.exp (-beta) *
        (Real.exp beta *
          quantumIsingClassicalCylinderPartition beta h (n + 1) ((A + 1) + (B + 1))) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = _ := by
      rw [← mul_assoc, ← Real.exp_add]
      simp


theorem quantumIsingClassicalCylinderPartition_pos
    (beta h : Real) (n L : Nat) :
    0 < quantumIsingClassicalCylinderPartition beta h n L := by
  unfold quantumIsingClassicalCylinderPartition
  apply Finset.sum_pos
  · intro omega _
    unfold quantumIsingClassicalCylinderWeight
    apply Finset.prod_pos
    intro t _
    unfold quantumIsingSpatialTrotterWeight quantumIsingVerticalBondWeight
    positivity
  · exact Finset.univ_nonempty


end StatMech.FrontierA
