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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part93
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingleton_of_residualCaseShareBudget
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                ∀ x ∈ liveOptions,
                  ∃ residualShare residualDenominator : ℝ,
                    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
                      v β H Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n)))
                      residualShare residualDenominator ∧
                    residualShare * residualDenominator ≤
                      schedule.singletonShare β H Ωnz v x * R) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  dsimp only
  intro x hx
  rcases hn H hH Ω v hv x hx with
    ⟨residualShare, residualDenominator, hshare, hpayment⟩
  exact le_trans hshare.2 hpayment

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingleton_of_residualCaseLabelShareBudget
    {schedule : LiveSingletonOptionShareSchedule}
    {ι :
      {n : ℕ} →
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
          FK.boxVerts 3 n → Option (FK.boxVerts 3 n) → Type*}
    [∀ n Ω v x, Fintype (ι (n := n) Ω v x)]
    [∀ n Ω v x, DecidableEq (ι (n := n) Ω v x)]
    {label :
      ∀ {n : ℕ},
        (Ω : Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) →
          (v : FK.boxVerts 3 n) →
          (x : Option (FK.boxVerts 3 n)) →
            finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
              n v →
              ι Ω v x}
    (h :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                ∀ x ∈ liveOptions,
                  ∃ residualDenominator : ℝ,
                    ∃ labelShare : ι Ωnz v x → ℝ,
                      SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
                        v β H Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        (label Ωnz v x) labelShare residualDenominator ∧
                      (∑ i : ι Ωnz v x, labelShare i) *
                          residualDenominator ≤
                        schedule.singletonShare β H Ωnz v x * R) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  dsimp only
  intro x hx
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
  let R := D - paid
  rcases hn H hH Ω v hv x hx with
    ⟨residualDenominator, labelShare, hlabel, hpayment⟩
  have hbound :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ωnz v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
        schedule.singletonShare β H Ωnz v x * R :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_le_labelShareBudget
      (v := v) (β := β) (H := H) (Ω := Ωnz)
      (D := residualDenominator)
      (budget := schedule.singletonShare β H Ωnz v x * R)
      (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
      (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
      (label := label Ωnz v x) (labelShare := labelShare)
      hlabel hpayment
  simpa [Ωnz, cap, D, paid, R] using hbound

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingleton_of_residualCasePointwiseShareBudget
    {schedule : LiveSingletonOptionShareSchedule}
    (h :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                ∀ x ∈ liveOptions,
                  ∃ residualDenominator : ℝ,
                    ∃ atomShare :
                      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData
                        n v → ℝ,
                      SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
                        v β H Ωnz true true true
                        ({x} : Finset (Option (FK.boxVerts 3 n)))
                        atomShare residualDenominator ∧
                      (∑ E ∈
                        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                          v Ωnz true true true
                          ({x} : Finset (Option (FK.boxVerts 3 n))),
                        atomShare E) * residualDenominator ≤
                        schedule.singletonShare β H Ωnz v x * R) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
      schedule := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  dsimp only
  intro x hx
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
  let R := D - paid
  rcases hn H hH Ω v hv x hx with
    ⟨residualDenominator, atomShare, hpointwise, hpayment⟩
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_le_pointwiseShareBudget
      (v := v) (β := β) (H := H) (Ω := Ωnz)
      (D := residualDenominator)
      (budget := schedule.singletonShare β H Ωnz v x * R)
      (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
      (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
      (atomShare := atomShare) hpointwise
      (by simpa [Ωnz, cap, D, paid, R] using hpayment)

set_option linter.style.longLine false in


theorem liveSingletonOptionShareScheduleSingleton_of_residualCaseNormalizedPointwiseRows
    {schedule : LiveSingletonOptionShareSchedule}
    (hR :
      BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleRemainderPositiveSubcritical
        schedule)
    (hpayment :
      ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
        ∀ᶠ n in atTop,
          ∀ H : ℝ, 0 < H →
            ∀ Ω : Finset
              (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ),
              ∀ v, ∀ _hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
                let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
                let cap := boundaryCrossingCap n Ωnz
                let D :=
                  finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct
                    β H n v
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
                ∀ x ∈ liveOptions,
                  (∑ E ∈
                    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
                      v Ωnz true true true
                      ({x} : Finset (Option (FK.boxVerts 3 n))),
                    finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                      β H E / R) ≤
                    schedule.singletonShare β H Ωnz v x) :
    BoundaryFiberWeightNonzeroCutoffSourcePairWithNonTwoPointClassifiedCoefficientSourceClassSupportResidualThresholdSupportExactCardCanonicalLabelFreeRawBudget15BoundaryCrossingRemainderExactShellConcreteIccExactCardImageCanonicalSplitGhostOriginEndpointCardOneLiveSingletonOptionShareScheduleSingletonPositiveSubcritical
      schedule := by
  refine
    liveSingletonOptionShareScheduleSingleton_of_residualCasePointwiseShareBudget
      (schedule := schedule) ?_
  intro β hβpos hβc
  filter_upwards [hR β hβpos hβc, hpayment β hβpos hβc] with
    n hnR hnPayment
  intro H hH Ω v hv
  dsimp only
  intro x hx
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
  let R := D - paid
  have hRpos : 0 < R := by
    simpa [Ωnz, cap, D, paid, R] using hnR H hH Ω v hv
  refine
    ⟨R,
      fun E => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
        β H E / R,
      ?_, ?_⟩
  · exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare_of_denominatorPositive
        (v := v) (β := β) (H := H) (D := R) (Ω := Ωnz)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (R := ({x} : Finset (Option (FK.boxVerts 3 n))))
        (le_of_lt hβpos) (le_of_lt hH) (hDpos := hRpos)
  · have hshare :
        (∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ωnz true true true
            ({x} : Finset (Option (FK.boxVerts 3 n))),
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / R) ≤
          schedule.singletonShare β H Ωnz v x := by
      simpa [Ωnz, cap, D, paid, R] using
        hnPayment H hH Ω v hv x hx
    exact mul_le_mul_of_nonneg_right hshare (le_of_lt hRpos)

end Exact3D
end StatMech
