/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part2
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleBalancedPartitionSum_eq_fiberSum
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleBalancedPartitionSum N M c =
      ∑ ξω : SixVertexRectangleBalancedBoundaryFibers N M,
        ξω.2.1.weight c := by
  rw [sixVertexRectangleBalancedPartitionSum]
  simp_rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  calc
    (∑ ξ : SixVertexToroidalBoundary N M,
      if ξ.Balanced then
        ∑ ω : SixVertexRectangleBoundaryFiber
          (sixVertexToroidalRectangleBoundary ξ), ω.1.weight c
      else 0) =
        ∑ ξ ∈ Finset.univ.filter
            (fun ξ : SixVertexToroidalBoundary N M => ξ.Balanced),
          ∑ ω : SixVertexRectangleBoundaryFiber
            (sixVertexToroidalRectangleBoundary ξ), ω.1.weight c := by
      rw [Finset.sum_filter]
    _ = ∑ ξ : {ξ : SixVertexToroidalBoundary N M // ξ.Balanced},
          ∑ ω : SixVertexRectangleBoundaryFiber
            (sixVertexToroidalRectangleBoundary ξ.1), ω.1.weight c := by
      rw [Finset.sum_subtype
        (p := fun ξ : SixVertexToroidalBoundary N M => ξ.Balanced)
        (Finset.univ.filter
          fun ξ : SixVertexToroidalBoundary N M => ξ.Balanced) (by simp)]
    _ = ∑ ξω : SixVertexRectangleBalancedBoundaryFibers N M,
          ξω.2.1.weight c := by
      rw [Fintype.sum_sigma]


end StatMech.FrontierD
