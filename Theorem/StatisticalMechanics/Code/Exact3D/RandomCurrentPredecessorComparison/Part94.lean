/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part86
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBound, relaxedBudget, hcover, hpoint, hrelax,
      htotal⟩
  exact
    finset_sum_le_of_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
      (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0))
      (fun m =>
        (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
          doubledBoxResidualMomentBranchSummand β n v w e0 m)
      caseOf caseSet rowBound relaxedBudget hcover hpoint hrelax htotal

end Exact3D
end StatMech
