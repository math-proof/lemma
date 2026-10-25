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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part98
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleStrictTotal_of_residualCaseNormalizedPointwiseRowsCanonicalRaw
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical)
    (hraw :
      LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalRawStrictTotalPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleStrictTotalPositiveSubcritical
      liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical := by
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hraw β hβpos hβc] with
    n hnR hnRaw
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap := boundaryCrossingCap n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  let paid :=
    cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
      cap *
        finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  let R := D - paid
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ωnz true true true
  let remaining :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
      β H n Ωnz v
  let tail :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
      β H n Ωnz v
  let row : Option (FK.boxVerts 3 n) → ℝ := fun x =>
    ∑ E ∈
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ωnz true true true
        ({x} : Finset (Option (FK.boxVerts 3 n))),
      finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  have hraw' :
      remaining + ((∑ x ∈ liveOptions, row x) + tail) < R := by
    simpa [Ωnz, cap, D, paid, R, liveOptions, remaining, tail, row] using
      hnRaw H hH Ω v hv
  have hshare :=
    liveSingletonOptionStrictTotalShare_lt_one_of_rawNumerator_lt
      liveOptions R remaining tail row hRpos hraw'
  simpa [liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRowsCanonical,
    liveSingletonOptionShareScheduleOfResidualCaseNormalizedPointwiseRows,
    liveSingletonOptionNormalizedRemainingShare, liveSingletonOptionNormalizedTailShare,
    Finset.sum_div, Ωnz, cap, D, paid, R, liveOptions, remaining, tail, row] using
    hshare

end Exact3D
end StatMech
