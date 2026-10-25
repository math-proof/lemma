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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part120
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15_of_residualBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15WeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15
      β H n Ωnz v
  refine
    ⟨B.four_none, B.four_endpoint, B.four_origin,
      B.four_origin_endpoint, B.four_ghost, B.four_ghost_endpoint,
      B.four_ghost_origin, B.four_ghost_origin_endpoint,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false false false
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false false true
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false true false
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false true true
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true false false
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true false true
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true true false
  · simpa [B, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualCardImageSourceClassSum]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_fourPlus_sum_le_markedResidualCardImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true true true
  · simpa [B, Ωnz] using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_auxiliaryTwoSourceBudget15
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15_of_residualBudget15
      h)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_residualBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualBudget15 h)

end Exact3D
end StatMech
