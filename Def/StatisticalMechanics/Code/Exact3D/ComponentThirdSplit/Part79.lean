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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part75
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneSingletonUniformCapFullBoxVolumeTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let cap := boundaryCrossingCap n Ωnz
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let paid :=
              cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                    β H n +
                cap *
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                    β H n v +
                finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v
            ∃ singletonCap : ℝ,
              0 ≤ singletonCap ∧
                (∀ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
                  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                    β H n Ωnz v
                    (finiteBoundaryGhostSourceClassEndpointMarkedSources
                        v true true true ∪
                      ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
                    singletonCap) ∧
                  finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                      β H n Ωnz v +
                    ((((2 * n + 1) ^ 3 : ℕ) : ℝ) * singletonCap +
                      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                        β H n Ωnz v) < D - paid

end Exact3D
end StatMech
