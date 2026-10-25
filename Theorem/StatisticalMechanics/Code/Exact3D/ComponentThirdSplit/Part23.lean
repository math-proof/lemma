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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part23
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithInactiveRemainderWeightNonzero_of_sourceActiveProfile
    (hactive :
      BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWithInactiveRemainderWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hactive β hβpos hβc] with n hnactive
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hactivev :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [
      Ωnz,
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution]
      using hnactive H hH Ω v hv
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ωnz v =
        ∑ a ∈
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
            n Ωnz v,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a :=
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
        β H n Ωnz v).symm
    _ =
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v +
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
            β H n Ωnz v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexSigma_sourceSplit
        β H n Ωnz v
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
            β H n Ωnz v +
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
            β H n Ωnz v :=
      add_le_add hactivev (le_refl
        (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
          β H n Ωnz v))

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithInactiveRemainderWeightNonzero :
    BoundaryVertexDecrementedSourceProfileMajorizationWithInactiveRemainderWeightNonzeroPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorizationWithInactiveRemainderWeightNonzero_of_sourceActiveProfile
    sourceActiveSigmaProfileWeightNonzeroBranch

end Exact3D
end StatMech
