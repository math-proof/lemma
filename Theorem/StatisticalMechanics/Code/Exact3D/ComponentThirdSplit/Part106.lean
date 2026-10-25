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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part111
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictShareScheduleAbsorption_of_components
    {oneShare boundaryPairShare emptyBoundaryShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryCrossingCapComponentStrictShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare) :
    BoundaryCrossingCapComponentStrictShareScheduleAbsorptionPositiveSubcritical
      oneShare boundaryPairShare emptyBoundaryShare := by
  intro β hβpos hβc
  filter_upwards [
    hbudget β hβpos hβc,
    hone β hβpos hβc,
    hboundary β hβpos hβc,
    hempty β hβpos hβc] with
    n hnbudget hnone hnboundary hnempty
  intro H hH Ω v hv
  rcases hnbudget H hH Ω v hv with
    ⟨honeShare, hboundaryShare, hemptyShare, hshareSum⟩
  exact
    ⟨honeShare, hboundaryShare, hemptyShare, hshareSum,
      hnone H hH Ω v hv, hnboundary H hH Ω v hv,
      hnempty H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem boundaryCrossingCapComponentStrictShareAbsorption_of_shareSchedule
    {oneShare boundaryPairShare emptyBoundaryShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (h :
      BoundaryCrossingCapComponentStrictShareScheduleAbsorptionPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare) :
    BoundaryCrossingCapComponentStrictSharePositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  exact
    ⟨oneShare β H n Ωnz v,
      boundaryPairShare β H n Ωnz v,
      emptyBoundaryShare β H n Ωnz v,
      hn H hH Ω v hv⟩

end Exact3D
end StatMech
