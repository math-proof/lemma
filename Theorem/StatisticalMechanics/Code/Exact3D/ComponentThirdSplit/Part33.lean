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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part35
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_explicitLiveEndpointMembershipBudget15
    (hbudget :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hbudget β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  rcases hn H hH Ω v hv with ⟨B, hcase, htotal⟩
  have hcase' :
      ∀ c,
        c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset →
          (∑ S ∈
            (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
              n Ωnz v).filter
              (fun S =>
                finiteBoundaryGhostSourceClassEndpointMembershipCase v S = c),
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ωnz v S) ≤
            B.toBudget c := by
    intro c hc
    simpa [sourceClassSupport, Ωnz] using hcase c hc
  have htotal' :
      (∑ c ∈ finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
        B.toBudget c) ≤ slack := by
    rw [SourceClassEndpointMembershipLiveBudget15.sum_liveCaseFinset_toBudget]
    exact htotal
  exact
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_le_of_sourceClassSupport_liveEndpointMembership_sum_le
      β H n Ωnz v hv (A := B.toBudget) (C := slack) hcase' htotal'

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudget_of_explicitLiveEndpointMembershipBudget15
    (hbudget :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudgetWeightNonzeroPositiveSubcritical :=
  sourceClassSupportBudget_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_explicitLiveEndpointMembershipBudget15
      hbudget)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_explicitLiveEndpointMembershipBudget15
    (hbudget :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_explicitLiveEndpointMembershipBudget15
      hbudget)

end Exact3D
end StatMech
