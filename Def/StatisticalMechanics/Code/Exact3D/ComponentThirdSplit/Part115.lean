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
import Abbrev.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part4
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def residualThresholdShellBudget15BoundaryCrossingRemainderCanonicalShareSchedule :
    ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule :=
  fun β H n Ω v =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
    let B :=
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v
    let R :=
      D -
        (cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
            β H n v)
    SourceClassEndpointMembershipLiveBudget15.normalized B R

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderShareScheduleAbsorptionPositiveSubcritical
    (sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule) :
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
            let R :=
              D -
                (cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v)
            SourceClassEndpointMembershipLiveBudget15.Nonneg
                (sectorShare β H n Ωnz v) ∧
              (sectorShare β H n Ωnz v).total ≤ 1 ∧
              SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
                B (sectorShare β H n Ωnz v) R

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdShellBudget15BoundaryCrossingRemainderStrictShareScheduleAbsorptionPositiveSubcritical
    (sectorShare :
      ResidualThresholdShellBudget15BoundaryCrossingRemainderShareSchedule) :
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
            let R :=
              D -
                (cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
                      β H n +
                  cap *
                    finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
                      β H n v +
                  finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                    β H n v)
            SourceClassEndpointMembershipLiveBudget15.Nonneg
                (sectorShare β H n Ωnz v) ∧
              (sectorShare β H n Ωnz v).total < 1 ∧
              SourceClassEndpointMembershipLiveBudget15.FieldwiseLeMul
                B (sectorShare β H n Ωnz v) R

end Exact3D
end StatMech
