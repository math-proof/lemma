/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part100
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsAt_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityTotalSelectedCopySixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityTotalSelectedCopySixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only at hbounds ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  let Fempty : Profile → ℝ :=
    fun m =>
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand β n
          v w e0 m
  let Finner : Profile → ℝ :=
    fun m =>
      β *
        doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand
          β n v w e0 m
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyTotal, hinnerTotal⟩
  constructor
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωtouch (fun m => m) Ωtouch
          (fun m =>
            β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m) =
          ∑ m ∈ Ωtouch,
            (β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m) := by
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ = ∑ m ∈ Ωtouch, Fempty m := by
        refine Finset.sum_congr rfl ?_
        intro m _hm
        simp [Fempty,
          doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_eq_inCurrent_add_outsideCurrent]
        ring
      _ =
          ∑ S ∈ supportPatterns,
            ∑ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              Fempty m := by
        simpa [Ωtouch, Ωactive, supportPatterns, Fempty, w] using
          doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
            (n := n) Ωactive Fempty
      _ ≤
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                Fempty m := by
        simpa [Ωactive, supportPatterns, Fempty, w] using
          beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardEmptySourcePairSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
            (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
            (e0 := e0) hedge Ω
      _ ≤
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
            6 := by
        simpa [Ωactive, supportPatterns, Fempty, w] using hemptyTotal
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωtouch (fun m => m) Ωtouch
          (fun m =>
            β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m) =
          ∑ m ∈ Ωtouch,
            (β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m) := by
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ = ∑ m ∈ Ωtouch, Finner m := by
        refine Finset.sum_congr rfl ?_
        intro m _hm
        simp [Finner,
          doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_inCurrent_add_outsideCurrent]
        ring
      _ =
          ∑ S ∈ supportPatterns,
            ∑ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              Finner m := by
        simpa [Ωtouch, Ωactive, supportPatterns, Finner, w] using
          doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
            (n := n) Ωactive Finner
      _ ≤
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                Finner m := by
        simpa [Ωactive, supportPatterns, Finner, w] using
          beta_mul_doubledBoxSwitchedSelectedCopyTotalPairCardInnerPairSourcePairSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
            (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
            (e0 := e0) hedge Ω
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6 := by
        simpa [Ωactive, supportPatterns, Finner, w] using hinnerTotal

end Exact3D
end StatMech
