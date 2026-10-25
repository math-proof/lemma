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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part5
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_sigmaGhostEdgeMultiplicitySplit
    (hlow :
      BoundaryVertexDecrementedSourceLowGhostMultiplicitySigmaEmptyWeightNonzeroBranchPositiveSubcritical)
    (hres :
      BoundaryVertexDecrementedSourceResidualGhostMultiplicitySigmaMainWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hlow β hβpos hβc, hres β hβpos hβc] with
    n hnlow hnres
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let e := finiteBoundaryGhostBoundaryEdge n v
  let S :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
      n Ωnz v
  let P :
      Sigma (fun m :
        ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop :=
    fun a => a.1 e ≤ (1 : ℕ)
  have hlowv :
      (∑ a ∈ S.filter P,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    simpa [S, P, Ωnz, e] using hnlow H hH Ω v hv
  have hresv :
      (∑ a ∈ S.filter (fun a => ¬ P a),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
    simpa [S, P, Ωnz, e] using hnres H hH Ω v hv
  have hS :
      (∑ a ∈ S,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    refine
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_filter_le_filter_not_le
        β H S P hlowv hresv ?_
    rw [
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty]
    exact le_of_eq (by ring)
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ωnz v =
        ∑ a ∈ S,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a :=
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
        β H n Ωnz v).symm
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v :=
      hS

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_sigmaGhostEdgeMultiplicitySplit
    (hlow :
      BoundaryVertexDecrementedSourceLowGhostMultiplicitySigmaEmptyWeightNonzeroBranchPositiveSubcritical)
    (hres :
      BoundaryVertexDecrementedSourceResidualGhostMultiplicitySigmaMainWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzero
    (boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_sigmaGhostEdgeMultiplicitySplit
      hlow hres)

end Exact3D
end StatMech
