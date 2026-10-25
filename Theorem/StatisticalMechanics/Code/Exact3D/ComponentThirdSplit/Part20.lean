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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part20
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem activePlusNonTwoPointClassifiedCoefficient_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (hslack :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationActivePlusNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hslack β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hslackv :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
            β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v +
          (finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
              β H n Ωnz v -
            finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
              β H n Ωnz v) := by
        exact add_le_add le_rfl hslackv
    _ =
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
        β H n Ωnz v := by
        ring

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_activePlusNonTwoPointClassifiedCoefficient
    (hnon :
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hnon β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have htarget :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  linarith

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_iff_activePlusNonTwoPointClassifiedCoefficient :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical ↔
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical :=
  ⟨activePlusNonTwoPointClassifiedCoefficient_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack,
    inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_activePlusNonTwoPointClassifiedCoefficient⟩

end Exact3D
end StatMech
