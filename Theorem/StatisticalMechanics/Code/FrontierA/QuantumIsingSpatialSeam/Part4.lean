/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSpatialSeam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterCylinder.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingSpatialSeam.Part4
open scoped BigOperators


namespace StatMech.FrontierA

theorem quantumIsingTrotterKernel_nonneg
    (beta h : Real) (n : Nat) (hbh : 0 ≤ beta * h)
    (s t : Bool) : 0 ≤ quantumIsingTrotterKernel beta h n s t := by
  unfold quantumIsingTrotterKernel
  by_cases hst : s = t
  · rw [if_pos hst]
    norm_num
  · rw [if_neg hst]
    positivity

theorem quantumIsingOpenTrotterTransferKernel_nonneg
    (beta h : Real) (n L : Nat) (hbh : 0 ≤ beta * h)
    (sigma tau : QuantumIsingChainConfig (L + 1)) :
    0 ≤ quantumIsingOpenTrotterTransferKernel beta h n L sigma tau := by
  unfold quantumIsingOpenTrotterTransferKernel
  exact mul_nonneg (Real.exp_nonneg _) <|
    Finset.prod_nonneg fun i _ =>
      quantumIsingTrotterKernel_nonneg beta h n hbh (sigma i) (tau i)


theorem quantumIsingOpenTrotterTransferKernel_add
    (beta h : Real) (n L M : Nat)
    (sigma tau : QuantumIsingChainConfig (L + M + 2)) :
    quantumIsingOpenTrotterTransferKernel beta h n (L + M + 1) sigma tau =
      Real.exp (beta / (4 * (n : Real)) *
        (quantumIsingSpinSign
            ((quantumIsingLeftSpatialBlock L M sigma) (Fin.last L)) *
          quantumIsingSpinSign
            ((quantumIsingRightSpatialBlock L M sigma) 0))) *
        quantumIsingOpenTrotterTransferKernel beta h n L
          (quantumIsingLeftSpatialBlock L M sigma)
          (quantumIsingLeftSpatialBlock L M tau) *
        quantumIsingOpenTrotterTransferKernel beta h n M
          (quantumIsingRightSpatialBlock L M sigma)
          (quantumIsingRightSpatialBlock L M tau) := by
  unfold quantumIsingOpenTrotterTransferKernel
  unfold quantumIsingOpenSpatialTrotterWeight
  rw [quantumIsingOpenChainInteraction_add]
  rw [show beta / (4 * (n : Real)) *
      (quantumIsingOpenChainInteraction L
          (quantumIsingLeftSpatialBlock L M sigma) +
        quantumIsingSpinSign
            (quantumIsingLeftSpatialBlock L M sigma (Fin.last L)) *
          quantumIsingSpinSign
            (quantumIsingRightSpatialBlock L M sigma 0) +
        quantumIsingOpenChainInteraction M
          (quantumIsingRightSpatialBlock L M sigma)) =
      beta / (4 * (n : Real)) *
          (quantumIsingSpinSign
              (quantumIsingLeftSpatialBlock L M sigma (Fin.last L)) *
            quantumIsingSpinSign
              (quantumIsingRightSpatialBlock L M sigma 0)) +
        beta / (4 * (n : Real)) *
          quantumIsingOpenChainInteraction L
            (quantumIsingLeftSpatialBlock L M sigma) +
        beta / (4 * (n : Real)) *
          quantumIsingOpenChainInteraction M
            (quantumIsingRightSpatialBlock L M sigma) by ring]
  rw [Real.exp_add, Real.exp_add, quantumIsing_prod_spatial_add]
  simp only [quantumIsingLeftSpatialBlock, quantumIsingRightSpatialBlock]
  ring

theorem quantumIsingTrotterTransferKernel_le_exp_mul_open
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (sigma tau : QuantumIsingChainConfig (L + 1)) :
    quantumIsingTrotterTransferKernel beta h n (L + 1) sigma tau ≤
      Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenTrotterTransferKernel beta h n L sigma tau := by
  unfold quantumIsingTrotterTransferKernel
  unfold quantumIsingOpenTrotterTransferKernel
  have hp : 0 ≤ ∏ i : Fin (L + 1),
      quantumIsingTrotterKernel beta h n (sigma i) (tau i) :=
    Finset.prod_nonneg fun i _ =>
      quantumIsingTrotterKernel_nonneg beta h n hbh (sigma i) (tau i)
  calc
    quantumIsingSpatialTrotterWeight beta n (L + 1) sigma *
        ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) ≤
      (Real.exp (beta / (4 * (n : Real))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma) *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) :=
      mul_le_mul_of_nonneg_right
        (quantumIsingSpatialTrotterWeight_le_exp_mul_open
          beta n L hn hbeta sigma) hp
    _ = _ := by ring

theorem exp_neg_mul_open_le_quantumIsingTrotterTransferKernel
    (beta h : Real) (n L : Nat) (hn : n ≠ 0)
    (hbeta : 0 ≤ beta) (hbh : 0 ≤ beta * h)
    (sigma tau : QuantumIsingChainConfig (L + 1)) :
    Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenTrotterTransferKernel beta h n L sigma tau ≤
      quantumIsingTrotterTransferKernel beta h n (L + 1) sigma tau := by
  unfold quantumIsingTrotterTransferKernel
  unfold quantumIsingOpenTrotterTransferKernel
  calc
    Real.exp (-(beta / (4 * (n : Real)))) *
        (quantumIsingOpenSpatialTrotterWeight beta n L sigma *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i)) =
      (Real.exp (-(beta / (4 * (n : Real)))) *
        quantumIsingOpenSpatialTrotterWeight beta n L sigma) *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) := by ring
    _ ≤ quantumIsingSpatialTrotterWeight beta n (L + 1) sigma *
          ∏ i : Fin (L + 1), quantumIsingTrotterKernel beta h n (sigma i) (tau i) := by
      apply mul_le_mul_of_nonneg_right
      · exact exp_neg_mul_open_le_quantumIsingSpatialTrotterWeight
          beta n L hn hbeta sigma
      · exact Finset.prod_nonneg fun i _ =>
          quantumIsingTrotterKernel_nonneg beta h n hbh (sigma i) (tau i)


end StatMech.FrontierA
