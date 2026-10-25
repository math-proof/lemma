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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part121
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualBudget15_of_residualThresholdBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualBudget15WeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have htotal :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
        β H n Ωnz v).total ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  have hresidual :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15
        β H n Ωnz v).total ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    rw [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15_total_eq_threshold_total
        β H n Ωnz v hv]
    exact htotal
  simpa [Ωnz] using hresidual

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualThresholdBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualBudget15
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualBudget15_of_residualThresholdBudget15
      h)

end Exact3D
end StatMech
