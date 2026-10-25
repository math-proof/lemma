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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part34
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorption_of_budget15
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipBudget15ComponentSumAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportExplicitLiveEndpointMembershipComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨B, hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
      hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
      hfourGhostOrigin, hfourGhostOriginEndpoint, htotal⟩
  refine ⟨B.toBudget, ?_, ?_⟩
  · intro c hc
    simp only [
      finiteBoundaryGhostSourceClassEndpointMembershipLiveCaseFinset,
      finiteBoundaryGhostSourceClassEndpointMembershipLabel,
      Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using hzeroNone
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using htwoNone
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using htwoEndpoint
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using htwoOrigin
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using htwoGhost
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        htwoGhostEndpoint
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        htwoGhostOrigin
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using hfourNone
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        hfourEndpoint
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using hfourOrigin
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        hfourOriginEndpoint
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using hfourGhost
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        hfourGhostEndpoint
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        hfourGhostOrigin
    · simpa [
        finiteBoundaryGhostSourceClassEndpointMembershipLabel,
        SourceClassEndpointMembershipLiveBudget15.toBudget] using
        hfourGhostOriginEndpoint
  · rw [SourceClassEndpointMembershipLiveBudget15.sum_liveCaseFinset_toBudget]
    exact htotal

end Exact3D
end StatMech
