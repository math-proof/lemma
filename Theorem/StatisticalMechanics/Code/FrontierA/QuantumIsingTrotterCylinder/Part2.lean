/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2
import Theorem.StatisticalMechanics.Code.Onsager.TracePowWalk
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingTrotterTrace_eq_pathPartition
    (beta h : Real) (n L : Nat) [NeZero n] (hn : 0 < n) :
    ((quantumIsingTrotterTransferMatrix beta h n L) ^ n).trace =
      (quantumIsingTrotterPathPartition beta h n L : Complex) := by
  rw [StatMech.Onsager.ons_trace_pow_eq_walk_sum _ n hn]
  unfold quantumIsingTrotterPathPartition quantumIsingTrotterTransferMatrix
  simp_rw [quantumIsingCyclicSucc_eq_add_one]
  push_cast
  rfl


theorem quantumIsingTrotterTransferKernel_eq_classicalLayer
    (beta h : Real) (n L : Nat)
    (sigma tau : QuantumIsingChainConfig L)
    (hpos : 0 < beta * h / (2 * n)) :
    quantumIsingTrotterTransferKernel beta h n L sigma tau =
      (∏ _i : Fin L,
        Real.exp (-quantumIsingVerticalCoupling beta h n)) *
      (quantumIsingSpatialTrotterWeight beta n L sigma *
        ∏ i : Fin L, quantumIsingVerticalBondWeight beta h n
          (sigma i) (tau i)) := by
  classical
  unfold quantumIsingTrotterTransferKernel
  have hvertical :
      (∏ i : Fin L, quantumIsingTrotterKernel beta h n (sigma i) (tau i)) =
        (∏ _i : Fin L,
          Real.exp (-quantumIsingVerticalCoupling beta h n)) *
        ∏ i : Fin L, quantumIsingVerticalBondWeight beta h n
          (sigma i) (tau i) := by
    calc
      (∏ i : Fin L,
          quantumIsingTrotterKernel beta h n (sigma i) (tau i)) =
          ∏ i : Fin L,
            Real.exp (-quantumIsingVerticalCoupling beta h n) *
              quantumIsingVerticalBondWeight beta h n
                (sigma i) (tau i) := by
        apply Finset.prod_congr rfl
        intro i _
        exact quantumIsingTrotterKernel_eq_verticalWeight
          beta h n (sigma i) (tau i) hpos
      _ = _ := Finset.prod_mul_distrib
  rw [hvertical]
  ring


theorem quantumIsingTrotterPathWeight_eq_classical
    (beta h : Real) (n L : Nat)
    (omega : Fin n -> QuantumIsingChainConfig L)
    (hpos : 0 < beta * h / (2 * n)) :
    (∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n L
        (omega k) (omega (quantumIsingCyclicSucc k))) =
      quantumIsingTrotterNormalization beta h n L *
        quantumIsingClassicalCylinderWeight beta h n L omega := by
  classical
  unfold quantumIsingTrotterNormalization
  unfold quantumIsingClassicalCylinderWeight
  simp_rw [quantumIsingTrotterTransferKernel_eq_classicalLayer
    beta h n L _ _ hpos]
  rw [Finset.prod_mul_distrib]


theorem quantumIsingTrotterPathPartition_eq_classical
    (beta h : Real) (n L : Nat)
    (hpos : 0 < beta * h / (2 * n)) :
    quantumIsingTrotterPathPartition beta h n L =
      quantumIsingTrotterNormalization beta h n L *
        quantumIsingClassicalCylinderPartition beta h n L := by
  classical
  unfold quantumIsingTrotterPathPartition
  unfold quantumIsingClassicalCylinderPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  exact quantumIsingTrotterPathWeight_eq_classical beta h n L omega hpos


theorem quantumIsingTrotterNormalization_eq_pow
    (beta h : Real) (n L : Nat) :
    quantumIsingTrotterNormalization beta h n L =
      Real.exp (-quantumIsingVerticalCoupling beta h n) ^ (L * n) := by
  unfold quantumIsingTrotterNormalization
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [pow_mul]


theorem quantumIsingTrotterTrace_eq_classical
    (beta h : Real) (n L : Nat) [NeZero n] (hn : 0 < n)
    (hpos : 0 < beta * h / (2 * n)) :
    ((quantumIsingTrotterTransferMatrix beta h n L) ^ n).trace =
      (Real.exp (-quantumIsingVerticalCoupling beta h n) ^ (L * n) *
        quantumIsingClassicalCylinderPartition beta h n L : Real) := by
  rw [quantumIsingTrotterTrace_eq_pathPartition beta h n L hn,
    quantumIsingTrotterPathPartition_eq_classical beta h n L hpos,
    quantumIsingTrotterNormalization_eq_pow]

end StatMech.FrontierA
