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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part118
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportAuxiliaryTwoSourceBudget15ComponentSumAbsorption_of_residualBudget15
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportAuxiliaryTwoSourceBudget15ComponentSumAbsorptionPositiveSubcritical := by
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
  · simpa [B, Ωnz, finiteBoundaryGhostSourceClassEndpointMembershipResidualBudget15]
      using hn H hH Ω v hv

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption_of_auxiliaryTwoSourceBudget15
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportAuxiliaryTwoSourceBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
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
  refine
    ⟨B, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_zero_none_sum_le_emptySourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_none_sum_le_unmarkedPairImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_endpoint_sum_le_unmarkedPairImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_origin_sum_le_unmarkedPairImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_sum_le_unmarkedPairImageSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_endpoint_sum_le_pairSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v hv
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_endpointMembership_two_ghost_origin_sum_le_pairSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v hv
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourNone
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourEndpoint
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourOrigin
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourOriginEndpoint
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourGhost
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourGhostEndpoint
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourGhostOrigin
  · simpa [B,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using hfourGhostOriginEndpoint
  · simpa [B, Ωnz] using htotal

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption_of_residualBudget15
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical :=
  boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorption_of_auxiliaryTwoSourceBudget15
    (boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportAuxiliaryTwoSourceBudget15ComponentSumAbsorption_of_residualBudget15
      h)

end Exact3D
end StatMech
