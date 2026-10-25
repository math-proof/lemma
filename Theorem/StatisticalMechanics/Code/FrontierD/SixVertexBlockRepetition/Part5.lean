/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part4
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleMaxBalancedBoundaryContribution_exists
    (N M : ℕ) (c : ℝ) :
    ∃ ξ : SixVertexToroidalBoundary N M,
      (if ξ.Balanced then
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)
      else 0) =
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
  obtain ⟨ξ, hξ, hmax⟩ := Finset.mem_image.mp
    (Finset.max'_mem
      (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
        if ξ.Balanced then
          sixVertexRectangleBoundaryPartitionSum N M c
            (sixVertexToroidalRectangleBoundary ξ)
        else 0) _)
  exact ⟨ξ, hmax⟩

theorem sixVertexRectangleMaxBalancedBoundaryContribution_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
  obtain ⟨ξ, hξ⟩ :=
    sixVertexRectangleMaxBalancedBoundaryContribution_exists N M c
  rw [← hξ]
  split_ifs
  · exact sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _
  · exact le_rfl


theorem sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleBalancedPartitionSum N M c ≤
      (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
  rw [sixVertexRectangleBalancedPartitionSum]
  let f : SixVertexToroidalBoundary N M → ℝ := fun ξ =>
    if ξ.Balanced then
      sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ)
    else 0
  have hle (ξ : SixVertexToroidalBoundary N M) :
      f ξ ≤ sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
    unfold sixVertexRectangleMaxBalancedBoundaryContribution
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨ξ, Finset.mem_univ ξ, rfl⟩
  calc
    (∑ ξ : SixVertexToroidalBoundary N M,
      if ξ.Balanced then
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)
      else 0) = ∑ ξ, f ξ := rfl
    _ ≤ Fintype.card (SixVertexToroidalBoundary N M) •
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
      exact Finset.sum_le_card_nsmul Finset.univ f _ fun ξ hξ => hle ξ
    _ = (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
      rw [nsmul_eq_mul, sixVertexToroidalBoundary_card]
      norm_cast


theorem sixVertexRectangleBalancedPartitionSum_pow_blockCount_le
    {N M a b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hN : Even (N + 1)) :
    sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ^
        ((a + 1) * (b + 1)) ≤
      ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ ((a + 1) * (b + 1)) *
        sixVertexRectangleBalancedPartitionSum
          ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
  let Q := (a + 1) * (b + 1)
  let B := sixVertexRectangleMaxBalancedBoundaryContribution
    (N + 1) (M + 1) c
  have hbase : 0 ≤ sixVertexRectangleBalancedPartitionSum
      (N + 1) (M + 1) c :=
    sixVertexRectangleBalancedPartitionSum_nonneg _ _ hc
  have hselect := pow_le_pow_left₀ hbase
    (sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced
      (N + 1) (M + 1) c) Q
  obtain ⟨ξ, hξmax⟩ :=
    sixVertexRectangleMaxBalancedBoundaryContribution_exists
      (N + 1) (M + 1) c
  have hmaxpow : B ^ Q ≤
      sixVertexRectangleBalancedPartitionSum
        ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
    by_cases hbal : ξ.Balanced
    · have hB : B = sixVertexRectangleBoundaryPartitionSum
          (N + 1) (M + 1) c (sixVertexToroidalRectangleBoundary ξ) := by
        simpa [B, hbal] using hξmax.symm
      rw [hB]
      have hrepeated :=
        sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated
          (a := a) (b := b) hc ξ
      refine hrepeated.trans ?_
      unfold sixVertexRectangleBalancedPartitionSum
      have hsingle := Finset.single_le_sum
        (f := fun η : SixVertexToroidalBoundary
            ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) =>
          if η.Balanced then
            sixVertexRectangleBoundaryPartitionSum
              ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c
              (sixVertexToroidalRectangleBoundary η)
          else 0)
        (fun η hη => by
          dsimp
          split_ifs
          · exact sixVertexRectangleBoundaryPartitionSum_nonneg _ _ hc _
          · exact le_rfl)
        (Finset.mem_univ
          (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ))
      simpa [sixVertexRepeatToroidalBoundary_balanced hN ξ hbal] using hsingle
    · have hB : B = 0 := by
        simpa [B, hbal] using hξmax.symm
      rw [hB]
      simpa [Q] using
        (sixVertexRectangleBalancedPartitionSum_nonneg
          ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) hc)
  calc
    sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ^ Q ≤
        ((2 : ℝ) ^ ((N + 1) + (M + 1)) * B) ^ Q := hselect
    _ = ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ Q * B ^ Q := by
      rw [mul_pow]
    _ ≤ ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ Q *
        sixVertexRectangleBalancedPartitionSum
          ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
      gcongr


end StatMech.FrontierD
