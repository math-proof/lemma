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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part103
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapComponentMajorantResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonCanonicalMaxCapResidualCaseClassifiedCountTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
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
  let classifiedCount : ℝ :=
    ∑ R ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v 1,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ωnz true true true R).card : ℝ)
  rcases hn H hH Ω v hv with
    ⟨remainingBound, singletonMaxCapBound, tailBound,
      hremaining, hcapBound, htailBound, hstrict⟩
  have hcountNonneg : 0 ≤ classifiedCount := by
    dsimp [classifiedCount]
    exact Finset.sum_nonneg fun R _hR => Nat.cast_nonneg _
  have hcapMul :
      classifiedCount *
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
            β H n Ωnz v hv ≤
        classifiedCount * singletonMaxCapBound :=
    mul_le_mul_of_nonneg_left hcapBound hcountNonneg
  have htail :
      classifiedCount *
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
            β H n Ωnz v hv +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ωnz v ≤
        classifiedCount * singletonMaxCapBound + tailBound :=
    add_le_add hcapMul htailBound
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        (classifiedCount *
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
              β H n Ωnz v hv +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        remainingBound + (classifiedCount * singletonMaxCapBound + tailBound) :=
    add_le_add hremaining htail
  exact
    lt_of_le_of_lt hmono
      (by
        simpa [Ωnz, cap, D, paid, classifiedCount] using hstrict)

end Exact3D
end StatMech
