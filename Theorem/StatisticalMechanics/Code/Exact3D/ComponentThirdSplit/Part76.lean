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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part79
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    boundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorption_of_canonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFree
    (h :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical := by
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
  rcases hn H hH Ω v hv with ⟨singletonCap, hcap, hpoint, hstrict⟩
  refine ⟨singletonCap, hpoint, ?_⟩
  have hcount :
      ((((2 * n + 1) ^ 3 - 2 : ℕ) : ℝ)) ≤
        (((2 * n + 1) ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le ((2 * n + 1) ^ 3) 2
  have hmul :
      ((((2 * n + 1) ^ 3 - 2 : ℕ) : ℝ) * singletonCap) ≤
        (((2 * n + 1) ^ 3 : ℕ) : ℝ) * singletonCap :=
    mul_le_mul_of_nonneg_right hcount hcap
  have htail :
      ((((2 * n + 1) ^ 3 - 2 : ℕ) : ℝ) * singletonCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        (((2 * n + 1) ^ 3 : ℕ) : ℝ) * singletonCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v :=
    add_le_add hmul le_rfl
  have hmono :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ωnz v +
        ((((2 * n + 1) ^ 3 - 2 : ℕ) : ℝ) * singletonCap +
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
            β H n Ωnz v) ≤
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
            β H n Ωnz v +
          ((((2 * n + 1) ^ 3 : ℕ) : ℝ) * singletonCap +
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
              β H n Ωnz v) :=
    add_le_add le_rfl htail
  exact lt_of_le_of_lt hmono hstrict

end Exact3D
end StatMech
