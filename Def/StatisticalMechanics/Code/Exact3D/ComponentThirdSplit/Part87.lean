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
import Structure.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part4
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
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
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v ≤ budget.remainingBudget β H Ωnz v ∧
              finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                  β H n Ωnz v ≤ budget.tailBudget β H Ωnz v ∧
                (∀ x ∈ liveOptions,
                  finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                      β H n Ωnz v
                      (finiteBoundaryGhostSourceClassEndpointMarkedSources
                          v true true true ∪
                        ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
                    budget.singletonBudget β H Ωnz v x) ∧
                  budget.remainingBudget β H Ωnz v +
                      ((∑ x ∈ liveOptions,
                          budget.singletonBudget β H Ωnz v x) +
                        budget.tailBudget β H Ωnz v) <
                    D - paid

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleRemainingPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                β H n Ωnz v ≤ budget.remainingBudget β H Ωnz v

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleTailPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                β H n Ωnz v ≤ budget.tailBudget β H Ωnz v

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionComponentBudgetScheduleSingletonPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            ∀ x ∈ liveOptions,
              finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                  β H n Ωnz v
                  (finiteBoundaryGhostSourceClassEndpointMarkedSources
                      v true true true ∪
                    ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
                budget.singletonBudget β H Ωnz v x

set_option linter.style.longLine false in


def LiveSingletonOptionComponentBudgetScheduleResidualCaseShareBudgetPositiveSubcritical
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            ∀ x ∈ liveOptions,
              ∃ share D : ℝ,
                SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                  v β H Ωnz true true true
                  ({x} : Finset (Option (FK.boxVerts 3 n))) share D ∧
                share * D ≤ budget.singletonBudget β H Ωnz v x

end Exact3D
end StatMech
