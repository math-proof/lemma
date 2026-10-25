/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part6
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleBoundaryPartitionSum_le_maxToroidal
    (N M : ℕ) (c : ℝ) (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ) ≤
      sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
  classical
  unfold sixVertexRectangleMaxToroidalBoundaryPartitionSum
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨ξ, Finset.mem_univ ξ, rfl⟩

theorem sixVertexToroidalBoundary_card (N M : ℕ) :
    Fintype.card (SixVertexToroidalBoundary N M) = 2 ^ (N + M) := by
  simp [SixVertexToroidalBoundary, pow_add, mul_comm]


theorem sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleToroidalPartitionSum N M c ≤
      (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
  rw [sixVertexRectangleToroidalPartitionSum]
  calc
    ∑ ξ : SixVertexToroidalBoundary N M,
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)
        ≤ ∑ _ξ : SixVertexToroidalBoundary N M,
            sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
          apply Finset.sum_le_sum
          intro ξ hξ
          exact sixVertexRectangleBoundaryPartitionSum_le_maxToroidal N M c ξ
    _ = (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
      rw [Finset.sum_const, nsmul_eq_mul]
      congr 1
      simp only [Finset.card_univ]
      norm_cast
      exact sixVertexToroidalBoundary_card N M


theorem sixVertexRectangleMaxToroidalBoundary_exists
    (N M : ℕ) (c : ℝ) :
    ∃ ξ : SixVertexToroidalBoundary N M,
      sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ) =
        sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c := by
  obtain ⟨ξ, hξ, hmax⟩ := Finset.mem_image.mp
    (Finset.max'_mem
      (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)) _)
  exact ⟨ξ, hmax⟩

end StatMech.FrontierD
