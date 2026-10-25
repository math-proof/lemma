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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part3
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleAbsorptionPositiveSubcritical
    (oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule) :
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
            let B :=
              finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v
            0 ≤ oneShare β H n Ωnz v ∧
            0 ≤ boundaryPairShare β H n Ωnz v ∧
            0 ≤ emptyBoundaryShare β H n Ωnz v ∧
            0 ≤ shellBudgetShare β H n Ωnz v ∧
            oneShare β H n Ωnz v +
                boundaryPairShare β H n Ωnz v +
                emptyBoundaryShare β H n Ωnz v +
                shellBudgetShare β H n Ωnz v ≤ 1 ∧
            cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                  β H n ≤
              oneShare β H n Ωnz v * D ∧
            cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                  β H n v ≤
              boundaryPairShare β H n Ωnz v * D ∧
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                β H n v ≤
              emptyBoundaryShare β H n Ωnz v * D ∧
            B.total ≤ shellBudgetShare β H n Ωnz v * D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBudgetPositiveSubcritical
    (oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            0 ≤ oneShare β H n Ωnz v ∧
            0 ≤ boundaryPairShare β H n Ωnz v ∧
            0 ≤ emptyBoundaryShare β H n Ωnz v ∧
            0 ≤ shellBudgetShare β H n Ωnz v ∧
            oneShare β H n Ωnz v +
                boundaryPairShare β H n Ωnz v +
                emptyBoundaryShare β H n Ωnz v +
                shellBudgetShare β H n Ωnz v ≤ 1

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleOnePointPositiveSubcritical
    (oneShare : ResidualThresholdShellBudget15AggregateShareSchedule) :
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
            cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                  β H n ≤
              oneShare β H n Ωnz v * D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleBoundaryPairPositiveSubcritical
    (boundaryPairShare : ResidualThresholdShellBudget15AggregateShareSchedule) :
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
            cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                  β H n v ≤
              boundaryPairShare β H n Ωnz v * D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleEmptyBoundaryPositiveSubcritical
    (emptyBoundaryShare : ResidualThresholdShellBudget15AggregateShareSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                β H n v ≤
              emptyBoundaryShare β H n Ωnz v * D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15AggregateComponentShareScheduleShellBudgetPositiveSubcritical
    (shellBudgetShare : ResidualThresholdShellBudget15AggregateShareSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            let D :=
              finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
            let B :=
              finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v
            B.total ≤ shellBudgetShare β H n Ωnz v * D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleAbsorptionPositiveSubcritical
    (oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule) :
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
            let B :=
              finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
                β H n Ωnz v
            0 ≤ oneShare β H n Ωnz v ∧
            0 ≤ boundaryPairShare β H n Ωnz v ∧
            0 ≤ emptyBoundaryShare β H n Ωnz v ∧
            0 ≤ shellBudgetShare β H n Ωnz v ∧
            oneShare β H n Ωnz v +
                boundaryPairShare β H n Ωnz v +
                emptyBoundaryShare β H n Ωnz v +
                shellBudgetShare β H n Ωnz v < 1 ∧
            cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                  β H n ≤
              oneShare β H n Ωnz v * D ∧
            cap *
                finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                  β H n v ≤
              boundaryPairShare β H n Ωnz v * D ∧
            finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                β H n v ≤
              emptyBoundaryShare β H n Ωnz v * D ∧
            B.total ≤ shellBudgetShare β H n Ωnz v * D

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15StrictAggregateComponentShareScheduleBudgetPositiveSubcritical
    (oneShare boundaryPairShare emptyBoundaryShare shellBudgetShare :
      ResidualThresholdShellBudget15AggregateShareSchedule) :
    Prop :=
  ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
    ∀ᶠ n in atTop,
      ∀ H : ℝ, 0 < H →
        ∀ Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
          ∀ v, v ∈ Finset.univ.filter (FK.boxBoundary 3 n) →
            let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
            0 ≤ oneShare β H n Ωnz v ∧
            0 ≤ boundaryPairShare β H n Ωnz v ∧
            0 ≤ emptyBoundaryShare β H n Ωnz v ∧
            0 ≤ shellBudgetShare β H n Ωnz v ∧
            oneShare β H n Ωnz v +
                boundaryPairShare β H n Ωnz v +
                emptyBoundaryShare β H n Ωnz v +
                shellBudgetShare β H n Ωnz v < 1

end Exact3D
end StatMech
