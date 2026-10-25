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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part121
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def LiveSingletonOptionShareScheduleResidualCaseNormalizedPointwiseRowsCanonicalUnpaidRemainderReservoirSplitFallbackMixedCanonicalSlotCapacityDisjointChargeWeightNonzeroPositiveSubcritical :
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
            let mainTerm :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v
            let restoredCopy :=
              ∑ d ∈ I.image,
                finiteBoundaryGhostCollapsedTwoPointSourceDataWeight β H d
            let emptyBudget :=
              finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
            let mainGap :=
              fun d : finiteBoundaryGhostCollapsedTwoPointSourceData n v =>
                mainTerm -
                  (((d.toSourceData.1 (finiteBoundaryGhostBoundaryEdge n v) :
                    ℕ) : ℝ) *
                    finiteBoundaryGhostCollapsedTwoPointSourceDataWeight
                      β H d)
            let mainGapSum := ∑ d ∈ I.image, mainGap d
            let emptyGap := emptyBudget - restoredCopy
            let Slot :=
              Sum (finiteBoundaryGhostCollapsedTwoPointSourceData n v) Unit
            ¬ (R ≤ 0) →
              ¬ (R ≤ mainGapSum) →
                ¬ (R ≤ emptyGap) →
                  ∃ Atom : Type,
                    ∃ atoms : Finset Atom,
                      ∃ demand : Atom → ℝ,
                        let candidateSlots : Atom → Finset Slot :=
                          canonicalCapacityCandidateSlots
                            I.image mainGap emptyGap demand
                        (∀ a, a ∈ atoms → 0 ≤ demand a) ∧
                          R ≤ ∑ a ∈ atoms, demand a ∧
                            (∀ a, a ∈ atoms →
                              (candidateSlots a).Nonempty) ∧
                              (∀ a, a ∈ atoms → ∀ b, b ∈ atoms →
                                a ≠ b →
                                  Disjoint
                                    (candidateSlots a)
                                    (candidateSlots b))

end Exact3D
end StatMech
