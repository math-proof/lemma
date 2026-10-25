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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part4
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in

theorem lowGhostMultiplicityEmptyWeightNonzeroBranch_of_raw
    (hlow :
      BoundaryVertexDecrementedSourceLowGhostMultiplicityEmptyBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceLowGhostMultiplicityEmptyWeightNonzeroBranchPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hlow β hβpos hβc] with n hnlow
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let e := finiteBoundaryGhostBoundaryEdge n v
  simpa [Ωnz, e] using hnlow H hH Ωnz v hv

set_option linter.style.longLine false in

theorem residualGhostMultiplicityMainWeightNonzeroBranch_of_raw
    (hres :
      BoundaryVertexDecrementedSourceResidualGhostMultiplicityMainBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceResidualGhostMultiplicityMainWeightNonzeroBranchPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hres β hβpos hβc] with n hnres
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let e := finiteBoundaryGhostBoundaryEdge n v
  have hresv :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ωnz.filter (fun m => ¬ m e ≤ (1 : ℕ))) v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n
            (finiteBoundaryGhostWeightNonzeroCutoff β H n Ωnz) v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
    simpa [Ωnz, e] using hnres H hH Ωnz v hv
  simpa [Ωnz, finiteBoundaryGhostWeightNonzeroCutoff_idem] using hresv

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_ghostEdgeMultiplicitySplit
    (hlow :
      BoundaryVertexDecrementedSourceLowGhostMultiplicityEmptyWeightNonzeroBranchPositiveSubcritical)
    (hres :
      BoundaryVertexDecrementedSourceResidualGhostMultiplicityMainWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hlow β hβpos hβc, hres β hβpos hβc] with
    n hnlow hnres
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let e := finiteBoundaryGhostBoundaryEdge n v
  have hlowv :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ωnz.filter (fun m => m e ≤ (1 : ℕ))) v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    simpa [Ωnz, e] using hnlow H hH Ω v hv
  have hresv :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ωnz.filter (fun m => ¬ m e ≤ (1 : ℕ))) v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
    simpa [Ωnz, e] using hnres H hH Ω v hv
  refine
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_of_filter_le_filter_not_le
      β H n Ωnz v (fun m => m e ≤ (1 : ℕ))
      hlowv hresv ?_
  rw [
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty]
  exact le_of_eq (by ring)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzeroGhostEdgeMultiplicitySplit
    (hlow :
      BoundaryVertexDecrementedSourceLowGhostMultiplicityEmptyWeightNonzeroBranchPositiveSubcritical)
    (hres :
      BoundaryVertexDecrementedSourceResidualGhostMultiplicityMainWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzero
    (boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_ghostEdgeMultiplicitySplit
      hlow hres)

end Exact3D
end StatMech
