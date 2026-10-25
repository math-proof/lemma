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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part67
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorption_of_components
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorptionPositiveSubcritical
      oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare := by
  intro β hβpos hβc
  filter_upwards [
    hbudget β hβpos hβc,
    hone β hβpos hβc,
    hboundary β hβpos hβc,
    hempty β hβpos hβc,
    hshell β hβpos hβc] with
    n hnbudget hnone hnboundary hnempty hnshell
  intro H hH Ω v hv
  rcases hnbudget H hH Ω v hv with
    ⟨honeShare, hboundaryShare, hemptyShare, hshellShare, hshareStrict⟩
  exact
    ⟨honeShare, hboundaryShare, hemptyShare, hshellShare, hshareStrict,
      hnone H hH Ω v hv, hnboundary H hH Ω v hv,
      hnempty H hH Ω v hv, hnshell H hH Ω v hv⟩

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorption_of_components
    {oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule}
    (hbudget :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
        oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare)
    (hone :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
        oneShare)
    (hboundary :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
        boundaryPairShare)
    (hempty :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
        emptyBoundaryShare)
    (hshell :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
        shellBudgetShare) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
      oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare := by
  intro β hβpos hβc
  filter_upwards [
    hbudget β hβpos hβc,
    hone β hβpos hβc,
    hboundary β hβpos hβc,
    hempty β hβpos hβc,
    hshell β hβpos hβc] with
    n hnbudget hnone hnboundary hnempty hnshell
  intro H hH Ω v hv
  rcases hnbudget H hH Ω v hv with
    ⟨honeShare, hboundaryShare, hemptyShare, hshellShare, hshareSum⟩
  exact
    ⟨honeShare, hboundaryShare, hemptyShare, hshellShare, hshareSum,
      hnone H hH Ω v hv, hnboundary H hH Ω v hv,
      hnempty H hH Ω v hv, hnshell H hH Ω v hv⟩

end Exact3D
end StatMech
