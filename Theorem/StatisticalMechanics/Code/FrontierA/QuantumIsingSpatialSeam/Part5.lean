/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part5
open scoped BigOperators


namespace StatMech.FrontierA

theorem exp_trotterSeam_pow
    (beta : Real) (n : Nat) (hn : n ≠ 0) :
    Real.exp (beta / (4 * (n : Real))) ^ n = Real.exp (beta / 4) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hn]

theorem exp_neg_trotterSeam_pow
    (beta : Real) (n : Nat) (hn : n ≠ 0) :
    Real.exp (-(beta / (4 * (n : Real)))) ^ n = Real.exp (-(beta / 4)) := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp [hn]

theorem quantumIsingOpenTrotterPathWeight_join
    (beta h : Real) (n L M : Nat)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
        (fun k => quantumIsingSpatialJoin L M (omegaL k) (omegaM k)) =
      (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0)))) *
        quantumIsingOpenTrotterPathWeight beta h n L omegaL *
        quantumIsingOpenTrotterPathWeight beta h n M omegaM := by
  unfold quantumIsingOpenTrotterPathWeight
  simp_rw [quantumIsingOpenTrotterTransferKernel_add]
  simp only [quantumIsingLeftSpatialBlock_join,
    quantumIsingRightSpatialBlock_join]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]

theorem quantumIsing_bridgeProduct_le
    (beta : Real) (n L M : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
      (quantumIsingSpinSign (omegaL k (Fin.last L)) *
        quantumIsingSpinSign (omegaM k 0)))) ≤ Real.exp (beta / 4) := by
  calc
    (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0)))) ≤
      ∏ _k : Fin n, Real.exp (beta / (4 * (n : Real))) := by
        apply Finset.prod_le_prod
        · intro k _
          exact Real.exp_nonneg _
        · intro k _
          apply Real.exp_le_exp.mpr
          have habs := quantumIsingSpinSign_mul_abs
            (omegaL k (Fin.last L)) (omegaM k 0)
          have hsign := (abs_le.mp (le_of_eq habs)).2
          have hJ : 0 ≤ beta / (4 * (n : Real)) := by positivity
          nlinarith
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact exp_trotterSeam_pow beta n hn

theorem quantumIsing_exp_neg_le_bridgeProduct
    (beta : Real) (n L M : Nat) (hn : n ≠ 0) (hbeta : 0 ≤ beta)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    Real.exp (-(beta / 4)) ≤
      ∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0))) := by
  calc
    Real.exp (-(beta / 4)) =
        ∏ _k : Fin n, Real.exp (-(beta / (4 * (n : Real)))) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact (exp_neg_trotterSeam_pow beta n hn).symm
    _ ≤ ∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign (omegaL k (Fin.last L)) *
          quantumIsingSpinSign (omegaM k 0))) := by
      apply Finset.prod_le_prod
      · intro k _
        exact Real.exp_nonneg _
      · intro k _
        apply Real.exp_le_exp.mpr
        have habs := quantumIsingSpinSign_mul_abs
          (omegaL k (Fin.last L)) (omegaM k 0)
        have hsign := (abs_le.mp (le_of_eq habs)).1
        have hJ : 0 ≤ beta / (4 * (n : Real)) := by positivity
        nlinarith

theorem quantumIsingOpenTrotterPathWeight_nonneg
    (beta h : Real) (n L : Nat) (hbh : 0 ≤ beta * h)
    (omega : Fin n -> QuantumIsingChainConfig (L + 1)) :
    0 ≤ quantumIsingOpenTrotterPathWeight beta h n L omega := by
  unfold quantumIsingOpenTrotterPathWeight
  exact Finset.prod_nonneg fun k _ =>
    quantumIsingOpenTrotterTransferKernel_nonneg beta h n L hbh _ _

theorem quantumIsingOpenTrotterPathWeight_join_le
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
        (fun k => quantumIsingSpatialJoin L M (omegaL k) (omegaM k)) ≤
      Real.exp (beta / 4) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) := by
  rw [quantumIsingOpenTrotterPathWeight_join]
  calc
    (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
          (quantumIsingSpinSign (omegaL k (Fin.last L)) *
            quantumIsingSpinSign (omegaM k 0)))) *
        quantumIsingOpenTrotterPathWeight beta h n L omegaL *
        quantumIsingOpenTrotterPathWeight beta h n M omegaM =
      (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
          (quantumIsingSpinSign (omegaL k (Fin.last L)) *
            quantumIsingSpinSign (omegaM k 0)))) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right
      · exact quantumIsing_bridgeProduct_le beta n L M hn hbeta omegaL omegaM
      · exact mul_nonneg
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n L hbh omegaL)
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n M hbh omegaM)

theorem quantumIsing_exp_mul_openPathWeights_le_join
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (omegaL : Fin n -> QuantumIsingChainConfig (L + 1))
    (omegaM : Fin n -> QuantumIsingChainConfig (M + 1)) :
    Real.exp (-(beta / 4)) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) ≤
      quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
        (fun k => quantumIsingSpatialJoin L M (omegaL k) (omegaM k)) := by
  rw [quantumIsingOpenTrotterPathWeight_join]
  calc
    Real.exp (-(beta / 4)) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) ≤
      (∏ k : Fin n, Real.exp (beta / (4 * (n : Real)) *
          (quantumIsingSpinSign (omegaL k (Fin.last L)) *
            quantumIsingSpinSign (omegaM k 0)))) *
        (quantumIsingOpenTrotterPathWeight beta h n L omegaL *
          quantumIsingOpenTrotterPathWeight beta h n M omegaM) := by
      apply mul_le_mul_of_nonneg_right
      · exact quantumIsing_exp_neg_le_bridgeProduct
          beta n L M hn hbeta omegaL omegaM
      · exact mul_nonneg
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n L hbh omegaL)
          (quantumIsingOpenTrotterPathWeight_nonneg beta h n M hbh omegaM)
    _ = _ := by ring

theorem quantumIsing_openPartition_reindex
    (beta h : Real) (n L M : Nat) :
    quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) =
      ∑ omega :
          (Fin n -> QuantumIsingChainConfig (L + 1)) ×
            (Fin n -> QuantumIsingChainConfig (M + 1)),
        quantumIsingOpenTrotterPathWeight beta h n (L + M + 1)
          ((quantumIsingSpatialPathEquiv n L M).symm omega) := by
  unfold quantumIsingOpenTrotterPathPartition
  apply Fintype.sum_equiv (quantumIsingSpatialPathEquiv n L M)
  intro omega
  simp

theorem quantumIsing_sum_pair_openPathWeights
    (beta h : Real) (n L M : Nat) :
    (∑ omega :
        (Fin n -> QuantumIsingChainConfig (L + 1)) ×
          (Fin n -> QuantumIsingChainConfig (M + 1)),
      quantumIsingOpenTrotterPathWeight beta h n L omega.1 *
        quantumIsingOpenTrotterPathWeight beta h n M omega.2) =
      quantumIsingOpenTrotterPathPartition beta h n L *
        quantumIsingOpenTrotterPathPartition beta h n M := by
  unfold quantumIsingOpenTrotterPathPartition
  calc
    (∑ omega :
        (Fin n -> QuantumIsingChainConfig (L + 1)) ×
          (Fin n -> QuantumIsingChainConfig (M + 1)),
      quantumIsingOpenTrotterPathWeight beta h n L omega.1 *
        quantumIsingOpenTrotterPathWeight beta h n M omega.2) =
      ∑ omegaL : Fin n -> QuantumIsingChainConfig (L + 1),
        ∑ omegaM : Fin n -> QuantumIsingChainConfig (M + 1),
          quantumIsingOpenTrotterPathWeight beta h n L omegaL *
            quantumIsingOpenTrotterPathWeight beta h n M omegaM := by
        exact Fintype.sum_prod_type _
    _ = _ := (Fintype.sum_mul_sum
      (quantumIsingOpenTrotterPathWeight beta h n L)
      (quantumIsingOpenTrotterPathWeight beta h n M)).symm


theorem quantumIsingOpenTrotterPathPartition_add_le
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) ≤
      Real.exp (beta / 4) *
        (quantumIsingOpenTrotterPathPartition beta h n L *
          quantumIsingOpenTrotterPathPartition beta h n M) := by
  rw [quantumIsing_openPartition_reindex]
  rw [← quantumIsing_sum_pair_openPathWeights]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  exact quantumIsingOpenTrotterPathWeight_join_le
    beta h n L M hn hbeta hbh omega.1 omega.2

theorem quantumIsing_exp_mul_openPartitions_le_add
    (beta h : Real) (n L M : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    Real.exp (-(beta / 4)) *
        (quantumIsingOpenTrotterPathPartition beta h n L *
          quantumIsingOpenTrotterPathPartition beta h n M) ≤
      quantumIsingOpenTrotterPathPartition beta h n (L + M + 1) := by
  rw [quantumIsing_openPartition_reindex]
  rw [← quantumIsing_sum_pair_openPathWeights]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  exact quantumIsing_exp_mul_openPathWeights_le_join
    beta h n L M hn hbeta hbh omega.1 omega.2


theorem quantumIsingTrotterPathPartition_le_exp_mul_open
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    quantumIsingTrotterPathPartition beta h n (L + 1) ≤
      Real.exp (beta / 4) *
        quantumIsingOpenTrotterPathPartition beta h n L := by
  unfold quantumIsingTrotterPathPartition
  unfold quantumIsingOpenTrotterPathPartition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    ∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n (L + 1)
        (omega k) (omega (quantumIsingCyclicSucc k)) ≤
      ∏ k : Fin n, (Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k))) := by
        apply Finset.prod_le_prod
        · intro k _
          unfold quantumIsingTrotterTransferKernel
          exact mul_nonneg (Real.exp_nonneg _) <|
            Finset.prod_nonneg fun i _ =>
              quantumIsingTrotterKernel_nonneg beta h n hbh _ _
        · intro k _
          exact quantumIsingTrotterTransferKernel_le_exp_mul_open
            beta h n L hn hbeta hbh _ _
    _ = Real.exp (beta / 4) *
        ∏ k : Fin n, quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [exp_trotterSeam_pow beta n hn]

theorem exp_neg_mul_open_le_quantumIsingTrotterPathPartition
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h) :
    Real.exp (-(beta / 4)) *
        quantumIsingOpenTrotterPathPartition beta h n L ≤
      quantumIsingTrotterPathPartition beta h n (L + 1) := by
  unfold quantumIsingTrotterPathPartition
  unfold quantumIsingOpenTrotterPathPartition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    Real.exp (-(beta / 4)) *
        ∏ k : Fin n, quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k)) =
      ∏ k : Fin n, (Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenTrotterTransferKernel beta h n L
          (omega k) (omega (quantumIsingCyclicSucc k))) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [exp_neg_trotterSeam_pow beta n hn]
    _ ≤ ∏ k : Fin n, quantumIsingTrotterTransferKernel beta h n (L + 1)
        (omega k) (omega (quantumIsingCyclicSucc k)) := by
      apply Finset.prod_le_prod
      · intro k _
        exact mul_nonneg (Real.exp_nonneg _)
          (quantumIsingOpenTrotterTransferKernel_nonneg beta h n L hbh _ _)
      · intro k _
        exact exp_neg_mul_open_le_quantumIsingTrotterTransferKernel
          beta h n L hn hbeta hbh _ _

theorem quantumIsingTrotterKernel_pos
    (beta h : Real) (n : Nat) (hn : n ≠ 0) (hbh : 0 < beta * h)
    (s t : Bool) : 0 < quantumIsingTrotterKernel beta h n s t := by
  unfold quantumIsingTrotterKernel
  by_cases hst : s = t
  · simp only [if_pos hst]
    norm_num
  · simp only [if_neg hst]
    positivity

theorem quantumIsingOpenTrotterPathWeight_pos
    (beta h : Real) (n L : Nat) (hn : n ≠ 0) (hbh : 0 < beta * h)
    (omega : Fin n -> QuantumIsingChainConfig (L + 1)) :
    0 < quantumIsingOpenTrotterPathWeight beta h n L omega := by
  unfold quantumIsingOpenTrotterPathWeight
  apply Finset.prod_pos
  intro k _
  unfold quantumIsingOpenTrotterTransferKernel
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro i _
  exact quantumIsingTrotterKernel_pos beta h n hn hbh _ _

theorem quantumIsingOpenTrotterPathPartition_pos
    (beta h : Real) (n L : Nat) (hn : n ≠ 0) (hbh : 0 < beta * h) :
    0 < quantumIsingOpenTrotterPathPartition beta h n L := by
  unfold quantumIsingOpenTrotterPathPartition
  apply Finset.sum_pos'
  · intro omega _
    exact (quantumIsingOpenTrotterPathWeight_pos beta h n L hn hbh omega).le
  · let omega : Fin n -> QuantumIsingChainConfig (L + 1) := fun _ _ => false
    exact ⟨omega, Finset.mem_univ _,
      quantumIsingOpenTrotterPathWeight_pos beta h n L hn hbh omega⟩


end StatMech.FrontierA
