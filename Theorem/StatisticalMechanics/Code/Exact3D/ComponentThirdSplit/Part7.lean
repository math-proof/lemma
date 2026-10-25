/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part6
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem sourceActiveCollapsedVertexTargetMultiplicityMainEmptyWeightNonzeroBranch :
    BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexTargetMultiplicityMainEmptyWeightNonzeroBranchPositiveSubcritical := by
  intro β hβpos _hβc
  filter_upwards [] with n
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  simpa [Ωnz, I] using
    finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_decrementedBoundaryMultiplicity_succ_weight_sum_le_image_card_mul_main_add_empty
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH)
      Ωnz hv

set_option linter.style.longLine false in


theorem collapsedVertexImageProfileWeightNonzeroBranch_of_targetMultiplicityMainEmpty
    (htarget :
      BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexTargetMultiplicityMainEmptyWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexImageProfileWeightNonzeroBranchPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [htarget β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
  have hfiber :
      (∑ d ∈ I.image,
          (((I.fiber d).card : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
        ∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) := by
    simpa [I] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_sum_le_decrementedBoundaryGhostMultiplicity_succ_weight_sum
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ωnz hv
  have htargetv :
      (∑ d ∈ I.image,
          (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) + 1 :
            ℕ) : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)) ≤
        (I.image.card : ℝ) *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    simpa [Ωnz, I] using hn H hH Ω v hv
  have hprofile :
      (I.image.card : ℝ) *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v := by
    simpa [I] using
      finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex_image_card_mul_main_add_empty_le_boundaryFiberSourcePairVertexProfile
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH)
        Ωnz hv
  simpa [Ωnz, I] using hfiber.trans (htargetv.trans hprofile)

set_option linter.style.longLine false in


theorem sourceActiveCollapsedVertexImageProfileWeightNonzeroBranch :
    BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexImageProfileWeightNonzeroBranchPositiveSubcritical :=
  collapsedVertexImageProfileWeightNonzeroBranch_of_targetMultiplicityMainEmpty
    sourceActiveCollapsedVertexTargetMultiplicityMainEmptyWeightNonzeroBranch

set_option linter.style.longLine false in


theorem sourceActiveCurrentProfileWeightNonzeroBranch_of_collapsedVertexImageProfile
    (himage :
      BoundaryVertexDecrementedSourceSourceActiveCollapsedVertexImageProfileWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceSourceActiveCurrentProfileWeightNonzeroBranchPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [himage β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have himagev :
      (∑ d ∈
          (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v).image,
          (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v).fiber
              d).card : ℝ) *
            finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
        (Ωnz.filter (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v =
      ∑ d ∈
          (finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v).image,
        (((finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v).fiber
            d).card : ℝ) *
          finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d := by
        exact
          finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_filter_fullSourceOnePoint_eq_collapsedVertexCutoffDecrementIndex_image_sum
            (β := β) (H := H) Ωnz v
    _ ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
        β H n Ωnz v := himagev

set_option linter.style.longLine false in


theorem sourceActiveCurrentProfileWeightNonzeroBranch :
    BoundaryVertexDecrementedSourceSourceActiveCurrentProfileWeightNonzeroBranchPositiveSubcritical :=
  sourceActiveCurrentProfileWeightNonzeroBranch_of_collapsedVertexImageProfile
    sourceActiveCollapsedVertexImageProfileWeightNonzeroBranch

end Exact3D
end StatMech
