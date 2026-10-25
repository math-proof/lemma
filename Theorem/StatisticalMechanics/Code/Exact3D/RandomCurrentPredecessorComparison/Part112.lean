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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part104
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt_of_ownerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt
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
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyShare, hinnerShare⟩
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
  · have hdecomp :
        (∑ S ∈ supportPatterns,
          ∑ m ∈ Ωactive.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            match doubledBoxOriginIncidentOwner n m with
            | none => 0
            | some ew =>
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                  β n v w e0 ew m) =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                  β n v w e0 ew m := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
      let F : Profile → ℝ :=
        fun m =>
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m
      calc
        (∑ m ∈ Ωactive.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m) =
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                F m := by
          simpa [F] using
            doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
              (n := n) Ωactive hSnonempty F
        _ =
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                  β n v w e0 ew m := by
          refine Finset.sum_congr rfl ?_
          intro ew _hew
          refine Finset.sum_congr rfl ?_
          intro m hm
          have howner :
              doubledBoxOriginIncidentOwner n m = some ew :=
            (Finset.mem_filter.mp hm).2.2
          simp [F, howner]
    calc
      (∑ S ∈ supportPatterns,
        ∑ m ∈ Ωactive.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m) =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                  β n v w e0 ew m := hdecomp
      _ ≤ (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
          6 := by
        simpa [supportPatterns, Ωactive, w] using
          doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
            (n := n)
            (F := fun S ew =>
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                  β n v w e0 ew m)
            (target :=
              (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
                6)
            hemptyTarget_nonneg
            (by
              intro S hS ew hew
              simpa [supportPatterns, Ωactive, w] using
                hemptyShare S (by simpa [supportPatterns] using hS) ew hew)
  · have hdecomp :
        (∑ S ∈ supportPatterns,
          ∑ m ∈ Ωactive.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            match doubledBoxOriginIncidentOwner n m with
            | none => 0
            | some ew =>
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                  β n v w e0 ew m) =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                  β n v w e0 ew m := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hSnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
      let F : Profile → ℝ :=
        fun m =>
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m
      calc
        (∑ m ∈ Ωactive.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m) =
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                F m := by
          simpa [F] using
            doubledBoxOriginIncidentSupport_filter_sum_eq_sum_supportPatternOwnerFilters
              (n := n) Ωactive hSnonempty F
        _ =
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                  β n v w e0 ew m := by
          refine Finset.sum_congr rfl ?_
          intro ew _hew
          refine Finset.sum_congr rfl ?_
          intro m hm
          have howner :
              doubledBoxOriginIncidentOwner n m = some ew :=
            (Finset.mem_filter.mp hm).2.2
          simp [F, howner]
    calc
      (∑ S ∈ supportPatterns,
        ∑ m ∈ Ωactive.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S),
          match doubledBoxOriginIncidentOwner n m with
          | none => 0
          | some ew =>
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m) =
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                  β n v w e0 ew m := hdecomp
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6 := by
        simpa [supportPatterns, Ωactive, w] using
          doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
            (n := n)
            (F := fun S ew =>
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    doubledBoxOriginIncidentSupport n m = S ∧
                      doubledBoxOriginIncidentOwner n m = some ew),
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                  β n v w e0 ew m)
            (target :=
              (β *
                Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w)) /
                6)
            hinnerTarget_nonneg
            (by
              intro S hS ew hew
              simpa [supportPatterns, Ωactive, w] using
                hinnerShare S (by simpa [supportPatterns] using hS) ew hew)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt_of_strictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt_of_ownerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_strictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
      hbounds)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt_of_atEdgeOwnerPairShareSixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityAtEdgeResidualBranchOwnerPairShareSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt
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
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyShare, hinnerShare⟩
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
  · simpa [Ωactive, supportPatterns, w] using
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_of_updateSelectedEdgeMultiplicity_pair_sums_le_div_384_strictSectorYPredecessor3
        (β := β)
        (target :=
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6)
        hβ hemptyTarget_nonneg (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge Ω
        (by
          intro S hS ew hew
          simpa [Ωactive, supportPatterns, w] using
            hemptyShare S (by simpa [supportPatterns] using hS) ew hew)
  · simpa [Ωactive, supportPatterns, w] using
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge_activeOriginIncidentSupportPatterns_sum_le_of_updateSelectedEdgeMultiplicity_pair_sums_le_div_384_strictSectorYPredecessor3
        (β := β)
        (target :=
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6)
        hβ hinnerTarget_nonneg (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) hedge Ω
        (by
          intro S hS ew hew
          simpa [Ωactive, supportPatterns, w] using
            hinnerShare S (by simpa [supportPatterns] using hS) ew hew)

end Exact3D
end StatMech
