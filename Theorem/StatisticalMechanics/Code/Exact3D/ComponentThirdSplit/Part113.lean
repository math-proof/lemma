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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part119
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15_of_auxiliaryTwoSourceBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15WeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨four_none, four_endpoint, four_origin, four_origin_endpoint,
      four_ghost, four_ghost_endpoint, four_ghost_origin,
      four_ghost_origin_endpoint, hfourNone, hfourEndpoint, hfourOrigin,
      hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint, htotal⟩
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15
      β H n Ωnz v
      four_none four_endpoint four_origin four_origin_endpoint
      four_ghost four_ghost_endpoint four_ghost_origin
      four_ghost_origin_endpoint
  refine ⟨B, ?_, ?_⟩
  · intro c hc
    simp only [
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
      finiteBoundaryGhostSourceClassEndpointMembershipLabel,
      Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_le_emptySourceClassSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_none_sum_le_unmarkedPairImageSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_endpoint_sum_le_unmarkedPairImageSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_sum_le_unmarkedPairImageSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_sum_le_unmarkedPairImageSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_endpoint_sum_le_pairSourceClassSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v hv
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_origin_sum_le_pairSourceClassSum
            (le_of_lt hβpos) (le_of_lt hH) n Ωnz v hv
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourNone
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourEndpoint
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourOrigin
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourOriginEndpoint
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourGhost
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourGhostEndpoint
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourGhostOrigin
    · simpa [B, sourceClassSupport,
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
        using hfourGhostOriginEndpoint
  · simpa [B, Ωnz] using htotal

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_auxiliaryTwoSourceBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_explicitLiveEndpointMembershipBudget15
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackExplicitLiveEndpointMembershipBudget15_of_auxiliaryTwoSourceBudget15
      h)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_auxiliaryTwoSourceBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackAuxiliaryTwoSourceBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_auxiliaryTwoSourceBudget15
      h)

end Exact3D
end StatMech
