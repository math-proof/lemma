/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part5
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum
    (T : EvenTorus) (c : ℝ) :
    sixVertexRectangleToroidalPartitionSum T.width T.height c =
      sixVertexTorusArrowPartitionSum T c := by
  classical
  rw [sixVertexRectangleToroidalPartitionSum, sixVertexTorusArrowPartitionSum]
  simp_rw [sixVertexRectangleBoundaryPartitionSum]
  calc
    ∑ ξ : SixVertexToroidalBoundary T.width T.height,
        ∑ ω : SixVertexRectangleArrows T.width T.height,
          (if sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ
          then ω.weight c else 0 : ℝ) =
      ∑ ξ : SixVertexToroidalBoundary T.width T.height,
        ∑ ω : {ω : SixVertexRectangleArrows T.width T.height //
          sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ},
          ω.1.weight c := by
        apply Finset.sum_congr rfl
        intro ξ hξ
        rw [← Finset.sum_subtype
          (Finset.univ.filter fun ω : SixVertexRectangleArrows T.width T.height =>
            sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ) (by simp)]
        exact (Finset.sum_filter _ _).symm
    _ = ∑ ξω : SixVertexCutRectangles T, ξω.2.1.weight c := by
      rw [Fintype.sum_sigma]
    _ = ∑ ω : SixVertexArrows T, ω.weight c := by
      symm
      calc
        ∑ ω : SixVertexArrows T, ω.weight c =
            ∑ ω : SixVertexArrows T, (sixVertexCutTorusArrows T ω).weight c := by
              apply Finset.sum_congr rfl
              intro ω hω
              exact (sixVertexCutTorusArrows_weight T c ω).symm
        _ = ∑ ξω : SixVertexCutRectangles T, ξω.2.1.weight c :=
          (sixVertexTorusCutEquiv T).sum_comp
            (fun ξω : SixVertexCutRectangles T => ξω.2.1.weight c)


theorem sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum
    (T : EvenTorus) {c : ℝ} (hc : 0 ≤ c) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c ≤
      sixVertexTorusArrowPartitionSum T c := by
  rw [← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
  exact sixVertexRectangleBalancedPartitionSum_le_toroidal
    T.width T.height hc


theorem sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary
    (T : EvenTorus) (c : ℝ) :
    sixVertexTorusArrowPartitionSum T c ≤
      (2 : ℝ) ^ (T.width + T.height) *
        sixVertexRectangleMaxToroidalBoundaryPartitionSum
          T.width T.height c := by
  rw [← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
  exact sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary
    T.width T.height c

end StatMech.FrontierD
