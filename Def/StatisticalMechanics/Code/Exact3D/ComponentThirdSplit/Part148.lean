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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part134
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def
    boundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardSourceBoundaryEdgeCombinedBudgetSchedule
    (cardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCardBudgetSchedule)
    (sourceCardBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioSourceCardBudgetSchedule)
    (edgeMultiplicityBudget :
      BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioBoundaryGhostEdgeMultiplicityBudgetSchedule) :
    BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCapBudgetSchedule :=
  fun β H n Ω v =>
    cardBudget β H n Ω v *
      (sourceCardBudget β H n Ω v *
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          edgeMultiplicityBudget β H n Ω v) *
        (((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) *
          edgeMultiplicityBudget β H n Ω v))

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioComponentShareUncutoffPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            ∃ oneShare boundaryPairShare emptyBoundaryShare : ℝ,
              0 ≤ oneShare ∧
              0 ≤ boundaryPairShare ∧
              0 ≤ emptyBoundaryShare ∧
              oneShare + boundaryPairShare + emptyBoundaryShare ≤ 1 ∧
              boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω *
                  boundaryVertexTanhNormalizedOnePointCurrentRatioTerm
                    β H n ≤
                oneShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω *
                  boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                    β H n v ≤
                boundaryPairShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
              emptyBoundaryShare * boundaryVertexBoxSimonCurrentRatio β n v

set_option linter.style.longLine false in


def BoundaryCrossingCapSourceSectorMultiplicitySquareBoxRatioCombinedEmptyShareUncutoffPositiveSubcritical :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            ∃ combinedShare emptyShare : ℝ,
              0 ≤ combinedShare ∧
              0 ≤ emptyShare ∧
              combinedShare + emptyShare ≤ 1 ∧
              boundaryCrossingCapSourceSectorMultiplicitySquareBound β H n Ω *
                  (boundaryVertexTanhNormalizedOnePointCurrentRatioTerm β H n +
                    boundaryVertexTanhNormalizedBoundaryPairCurrentRatioTerm
                      β H n v) ≤
                combinedShare * boundaryVertexBoxSimonCurrentRatio β n v ∧
              boundaryVertexTanhNormalizedEmptyBoundaryCurrentRatioTerm
                β H n v ≤
                emptyShare * boundaryVertexBoxSimonCurrentRatio β n v

end Exact3D
end StatMech
