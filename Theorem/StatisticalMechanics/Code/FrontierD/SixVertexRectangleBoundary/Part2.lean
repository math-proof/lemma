/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part5
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleBoundaryPartitionSum_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) (ξ : SixVertexRectangleBoundary N M) :
    0 ≤ sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  unfold sixVertexRectangleBoundaryPartitionSum
  apply Finset.sum_nonneg
  intro ω hω
  split_ifs
  · exact SixVertexRectangleArrows.weight_nonneg hc ω
  · exact le_rfl

theorem sixVertexRectangleToroidalPartitionSum_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ sixVertexRectangleToroidalPartitionSum N M c := by
  unfold sixVertexRectangleToroidalPartitionSum
  exact Finset.sum_nonneg fun ξ _ =>
    sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _

theorem sixVertexRectangleBalancedPartitionSum_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ sixVertexRectangleBalancedPartitionSum N M c := by
  unfold sixVertexRectangleBalancedPartitionSum
  apply Finset.sum_nonneg
  intro ξ hξ
  split_ifs
  · exact sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _
  · exact le_rfl


theorem sixVertexRectangleFreePartitionSum_eq_sum_boundary
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleFreePartitionSum N M c =
      ∑ ξ : SixVertexRectangleBoundary N M,
        sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  classical
  rw [sixVertexRectangleFreePartitionSum]
  simp_rw [sixVertexRectangleBoundaryPartitionSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω hω
  simp


theorem sixVertexRectangleBalancedPartitionSum_le_toroidal
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    sixVertexRectangleBalancedPartitionSum N M c ≤
      sixVertexRectangleToroidalPartitionSum N M c := by
  unfold sixVertexRectangleBalancedPartitionSum
  unfold sixVertexRectangleToroidalPartitionSum
  apply Finset.sum_le_sum
  intro ξ hξ
  split_ifs
  · exact le_rfl
  · exact sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _


end StatMech.FrontierD
