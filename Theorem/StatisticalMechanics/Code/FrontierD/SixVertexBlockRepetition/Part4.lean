/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part3
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleTileBlocksBoundaryFiber_injective
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
    Function.Injective
      (sixVertexRectangleTileBlocksBoundaryFiber (ξ := ξ) (a := a) (b := b)) := by
  intro ω η h
  apply sixVertexRectangleTileBlocks_injective
  exact congrArg Subtype.val h


theorem sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated
    {N M a b : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (ξ : SixVertexToroidalBoundary (N + 1) (M + 1)) :
    sixVertexRectangleBoundaryPartitionSum (N + 1) (M + 1) c
        (sixVertexToroidalRectangleBoundary ξ) ^ ((a + 1) * (b + 1)) ≤
      sixVertexRectangleBoundaryPartitionSum
        ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c
        (sixVertexToroidalRectangleBoundary
          (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)) := by
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum,
    Fintype.sum_pow]
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  let e := finProdFinEquiv (m := a + 1) (n := b + 1)
  let reindex := Equiv.arrowCongr e
    (Equiv.refl (SixVertexRectangleBoundaryFiber
      (sixVertexToroidalRectangleBoundary ξ)))
  let tile := sixVertexRectangleTileBlocksBoundaryFiber
    (ξ := ξ) (a := a) (b := b)
  calc
    (∑ p : Fin ((a + 1) * (b + 1)) →
          SixVertexRectangleBoundaryFiber
            (sixVertexToroidalRectangleBoundary ξ),
        ∏ i, (p i).1.weight c) =
        ∑ ω : SixVertexRectangleBlockCopies ξ a b,
          ∏ xy, (ω xy).1.weight c := by
      symm
      apply Fintype.sum_equiv reindex
      intro ω
      apply Fintype.prod_equiv e
      intro xy
      simp [reindex]
    _ = ∑ ω : SixVertexRectangleBlockCopies ξ a b,
          (tile ω).1.weight c := by
      apply Fintype.sum_congr
      intro ω
      exact (sixVertexRectangleTileBlocks_weight c ω).symm
    _ = ∑ η ∈ Finset.univ.image tile, η.1.weight c := by
      rw [Finset.sum_image
        (sixVertexRectangleTileBlocksBoundaryFiber_injective
          (ξ := ξ) (a := a) (b := b)).injOn]
    _ ≤ ∑ η : SixVertexRectangleBoundaryFiber
          (sixVertexToroidalRectangleBoundary
            (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)),
              η.1.weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro η hη hnot
        exact SixVertexRectangleArrows.weight_nonneg hc η.1


end StatMech.FrontierD
