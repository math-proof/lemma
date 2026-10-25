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
import Inductive.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part2
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

def unpaidRemainderReservoirBranchPredicate
    (branch : UnpaidRemainderReservoirBranch)
    (R mainGapSum emptyGap : ℝ) : Prop :=
  match branch with
  | UnpaidRemainderReservoirBranch.nonpositive => R ≤ 0
  | UnpaidRemainderReservoirBranch.mainGap => R ≤ mainGapSum
  | UnpaidRemainderReservoirBranch.emptyGap => R ≤ emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchCoverWeightNonzeroPositiveSubcritical :
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
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            ∃ branch : UnpaidRemainderReservoirBranch,
              unpaidRemainderReservoirBranchPredicate
                branch R mainGapSum emptyGap

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirBranchDisjunctionWeightNonzeroPositiveSubcritical :
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
            let R := D - paid
            let I := finiteBoundaryGhostCollapsedVertexCutoffDecrementIndex Ωnz v
            let mainGapSum :=
              ∑ d ∈ I.image,
                (finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
                    β H n v -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d))
            let emptyGap :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
                  β H n v -
                (∑ d ∈ I.image,
                  finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d)
            R ≤ 0 ∨ R ≤ mainGapSum ∨ R ≤ emptyGap

end Exact3D
end StatMech
