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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part105
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hbounds ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  let Fempty : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  let Finner : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyShare, hinnerShare⟩
  have hactiveTouch :
      Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m) =
        Ωactive := by
    simpa [Ωactive, w] using
      doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
  have hempty_decomp :
      (∑ m ∈ Ωactive, Fempty m) =
        ∑ S ∈ supportPatterns,
          ∑ ew ∈ S,
            ∑ m ∈
              Ωactive.filter
                (fun m =>
                  doubledBoxOriginIncidentSupport n m = S ∧
                    doubledBoxOriginIncidentOwner n m = some ew),
              Fempty m := by
    calc
      (∑ m ∈ Ωactive, Fempty m) =
          ∑ m ∈
            Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
            Fempty m := by
        rw [hactiveTouch]
      _ =
          ∑ S ∈ supportPatterns,
            ∑ m ∈
              Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              Fempty m := by
        simpa [supportPatterns] using
          doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
            (n := n) Ωactive Fempty
      _ =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈
                Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                Fempty m := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        have hS' :
            S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
              (fun S => S.Nonempty) := by
          simpa only [supportPatterns] using hS
        have hSnonempty : S.Nonempty :=
          (Finset.mem_filter.mp hS').2
        simpa using
          doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
            (n := n) Ωactive hSnonempty Fempty
  have hinner_decomp :
      (∑ m ∈ Ωactive, Finner m) =
        ∑ S ∈ supportPatterns,
          ∑ ew ∈ S,
            ∑ m ∈
              Ωactive.filter
                (fun m =>
                  doubledBoxOriginIncidentSupport n m = S ∧
                    doubledBoxOriginIncidentOwner n m = some ew),
              Finner m := by
    calc
      (∑ m ∈ Ωactive, Finner m) =
          ∑ m ∈
            Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m),
            Finner m := by
        rw [hactiveTouch]
      _ =
          ∑ S ∈ supportPatterns,
            ∑ m ∈
              Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              Finner m := by
        simpa [supportPatterns] using
          doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
            (n := n) Ωactive Finner
      _ =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈
                Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                Finner m := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        have hS' :
            S ∈ ((doubledBoxOriginIncidentEdges n).powerset).filter
              (fun S => S.Nonempty) := by
          simpa only [supportPatterns] using hS
        have hSnonempty : S.Nonempty :=
          (Finset.mem_filter.mp hS').2
        simpa using
          doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
            (n := n) Ωactive hSnonempty Finner
  have hemptyTarget_nonneg :
      0 ≤ (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
        6 := by
    exact div_nonneg
      (mul_nonneg hβ
        (doubledBoxOriginToInnerEndpointSourcePairEmptySum_nonneg hβ n v))
      (by norm_num)
  have hinnerTarget_nonneg :
      0 ≤
        (β *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6 := by
    exact div_nonneg
      (mul_nonneg hβ
        (doubledBoxInnerPairSourcePairSum_nonneg hβ n v w))
      (by norm_num)
  constructor
  · calc
      (∑ m ∈ Ωactive,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m) =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈
                Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                Fempty m := by
        simpa [Fempty] using hempty_decomp
      _ ≤ (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
          6 := by
        simpa [supportPatterns, Fempty] using
          doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
            (n := n)
            (F := fun S ew =>
              ∑ m ∈
                Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                Fempty m)
            (target :=
              (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
                6)
            hemptyTarget_nonneg
            (by
              intro S hS ew hew
              simpa [supportPatterns, Fempty, w] using
                hemptyShare S (by simpa [supportPatterns] using hS) ew hew)
  · calc
      (∑ m ∈ Ωactive,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m) =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈
                Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                Finner m := by
        simpa [Finner] using hinner_decomp
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6 := by
        simpa [supportPatterns, Finner] using
          doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
            (n := n)
            (F := fun S ew =>
              ∑ m ∈
                Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                Finner m)
            (target :=
              (β *
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w)) /
                6)
            hinnerTarget_nonneg
            (by
              intro S hS ew hew
              simpa [supportPatterns, Finner, w] using
                hinnerShare S (by simpa [supportPatterns] using hS) ew hew)

end Exact3D
end StatMech
