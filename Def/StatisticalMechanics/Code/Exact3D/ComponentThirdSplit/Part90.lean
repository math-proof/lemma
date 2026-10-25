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
import Structure.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part5
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionComponentBudgetScheduleOfShareSchedule
    (schedule : LiveSingletonOptionShareSchedule) :
    LiveSingletonOptionComponentBudgetSchedule where
  remainingBudget := fun {n} β H Ω v =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
    let paid :=
      cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
    schedule.remainingShare β H Ω v * (D - paid)
  tailBudget := fun {n} β H Ω v =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
    let paid :=
      cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
    schedule.tailShare β H Ω v * (D - paid)
  singletonBudget := fun {n} β H Ω v x =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
      let paid :=
        cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
              β H n +
          cap *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
      schedule.singletonShare β H Ω v x * (D - paid)

set_option linter.style.longLine false in


noncomputable def liveSingletonOptionShareScheduleOfComponentBudgetSchedule
    (budget : LiveSingletonOptionComponentBudgetSchedule) :
    LiveSingletonOptionShareSchedule where
  remainingShare := fun {n} β H Ω v =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
    let paid :=
      cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
    budget.remainingBudget β H Ω v / (D - paid)
  tailShare := fun {n} β H Ω v =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
    let paid :=
      cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
    budget.tailBudget β H Ω v / (D - paid)
  singletonShare := fun {n} β H Ω v x =>
    let cap := boundaryCrossingCap n Ω
    let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
    let paid :=
      cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
            β H n +
        cap *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
    budget.singletonBudget β H Ω v x / (D - paid)

set_option linter.style.longLine false in


def BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleTailStrictRemainderDenominatorFreeAbsorptionPositiveSubcritical
    (schedule : LiveSingletonOptionShareSchedule) :
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
            let R := D - paid
            let liveOptions :=
              finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
                v Ωnz true true true
            0 < R ∧
              0 ≤ schedule.remainingShare β H Ωnz v ∧
                0 ≤ schedule.tailShare β H Ωnz v ∧
                  (∀ x ∈ liveOptions,
                    0 ≤ schedule.singletonShare β H Ωnz v x) ∧
                    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
                        β H n Ωnz v ≤
                      schedule.remainingShare β H Ωnz v * R ∧
                      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
                          β H n Ωnz v ≤
                        schedule.tailShare β H Ωnz v * R ∧
                        (∀ x ∈ liveOptions,
                          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
                              β H n Ωnz v
                              (finiteBoundaryGhostSourceClassEndpointMarkedSources
                                  v true true true ∪
                                ({x} :
                                  Finset (Option (FK.boxVerts 3 n)))) ≤
                            schedule.singletonShare β H Ωnz v x * R) ∧
                        schedule.remainingShare β H Ωnz v +
                            ((∑ x ∈ liveOptions,
                                schedule.singletonShare β H Ωnz v x) +
                              schedule.tailShare β H Ωnz v) <
                            1

end Exact3D
end StatMech
