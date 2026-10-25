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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part168
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt_of_fourBetaContractionAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    {hvwedge : boxVertPositiveXFaceOrderedWedge3 n v}
    {hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))}
    {hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))}
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {hedge :
      e0.1 =
          s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
            FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))}
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionAt
        β n v hvwedge hlt hypos e0 hedge) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt
      β n v hvwedge hlt hypos e0 hedge := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases hcontract with ⟨hempty_contract, hinner_contract⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
        hβ n v w e0
  · have hfour :=
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSum
        hβ n v w e0
    calc
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) ≤
          (2 * β) *
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
        hfour
      _ =
          β *
            (2 *
              edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
                (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n v)
                (∅ : Finset (FK.boxVerts 3 (2 * n)))) := by
        ring
      _ ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
        exact mul_le_mul_of_nonneg_left hempty_contract hβ
  · exact
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
        hβ n v w e0
  · have hfour :=
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_tsum_le_two_beta_mul_four_beta_sourcePairSum
        hβ n v w e0
    calc
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0 m) ≤
          (2 * β) *
            edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) :=
        hfour
      _ =
          β *
            (2 *
              edgeCopySourcePairSum (FK.boxGraph 3 (2 * n)) (2 * (2 * β))
                (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
                (doubledBoxInnerPairSource n v w)) := by
        ring
      _ ≤
          β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
        exact mul_le_mul_of_nonneg_left hinner_contract hβ

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundsAt_of_fourBetaContractionsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt_of_fourBetaContractionAt
      hβ (hcontract v hvwedge hlt hypos e0 hedge)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt_of_fourBetaContractionsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt
      β n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hvwedge hlt hypos e0 hedge
    exact
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt_of_fourBetaContractionAt
        hβ (hcontract v hvwedge hlt hypos e0 hedge)).1
  · intro v hvwedge hlt hypos e0 hedge
    exact
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt_of_fourBetaContractionAt
        hβ (hcontract v hvwedge hlt hypos e0 hedge)).2.1
  · intro v hvwedge hlt hypos e0 hedge
    exact
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt_of_fourBetaContractionAt
        hβ (hcontract v hvwedge hlt hypos e0 hedge)).2.2.1
  · intro v hvwedge hlt hypos e0 hedge
    exact
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundAt_of_fourBetaContractionAt
        hβ (hcontract v hvwedge hlt hypos e0 hedge)).2.2.2

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_fourBetaContractionsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n := by
  have htsum :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt
        β n :=
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt_of_fourBetaContractionsAt
      hβ hcontract
  exact ⟨htsum.2.1, htsum.2.2.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_fourBetaContractionsPositiveSubcritical
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcontract β hβpos hβc) fun n hn =>
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_fourBetaContractionsAt
      hβpos.le hn

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical_of_fourBetaContractionsPositiveSubcritical
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcontract β hβpos hβc) fun n hn =>
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt_of_branchComponentBoundsAt
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_fourBetaContractionsAt
        hβpos.le hn)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical_of_fourBetaContractionsPositiveSubcritical
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeFourBetaContractionsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcontract β hβpos hβc) fun n hn =>
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt_of_branchComponentBoundsAt
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_fourBetaContractionsAt
        hβpos.le hn)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt_of_vertexEdgeTsumBoundsAt
    {β : ℝ} {n : ℕ}
    (hvertexEdge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentVertexEdgeTsumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt
      β n := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hvwedge hlt hypos e0 hedge
    exact (hvertexEdge v hvwedge hlt hypos e0 hedge).1
  · intro v hvwedge hlt hypos e0 hedge
    exact (hvertexEdge v hvwedge hlt hypos e0 hedge).2.1
  · intro v hvwedge hlt hypos e0 hedge
    exact (hvertexEdge v hvwedge hlt hypos e0 hedge).2.2.1
  · intro v hvwedge hlt hypos e0 hedge
    exact (hvertexEdge v hvwedge hlt hypos e0 hedge).2.2.2

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchTsumBoundAt_of_branchComponentTsumBoundAt
    {β : ℝ} {n : ℕ}
    (hcomponent :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentTsumBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchTsumBoundAt
      β n := by
  rcases hcomponent with ⟨hempty, hempty_bound, hinner, hinner_bound⟩
  refine ⟨hempty, hinner, ?_⟩
  intro v hvwedge hlt hypos e0 hedge
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m) +
      (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
        ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
          β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              (doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
            exact add_le_add
              (hempty_bound v hvwedge hlt hypos e0 hedge)
              (hinner_bound v hvwedge hlt hypos e0 hedge)
    _ =
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              (doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) := by
          ring

end Exact3D
end StatMech
