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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part101
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsAt_of_ownerPairShareSixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchOwnerPairShareSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
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
      doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
        (n := n)
        (F := fun S ew =>
          ∑ m ∈ Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n
              v w e0 m)
        (target :=
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6)
        hemptyTarget_nonneg
        (by
          intro S hS ew hew
          simpa [Ωactive, supportPatterns, w] using
            hemptyShare S (by simpa [supportPatterns] using hS) ew hew)
  · simpa [Ωactive, supportPatterns, w] using
      doubledBoxNonemptyOriginIncidentSupportPatternOwnerPairs_sum_le_of_forall_le_div_384
        (n := n)
        (F := fun S ew =>
          ∑ m ∈ Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0),
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m)
        (target :=
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6)
        hinnerTarget_nonneg
        (by
          intro S hS ew hew
          simpa [Ωactive, supportPatterns, w] using
            hinnerShare S (by simpa [supportPatterns] using hS) ew hew)

end Exact3D
end StatMech
