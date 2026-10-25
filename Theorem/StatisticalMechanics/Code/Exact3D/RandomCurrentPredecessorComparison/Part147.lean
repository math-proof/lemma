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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part139
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, hcoverEmpty, hcoverInner, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, hnonnegEmpty, hnonnegInner,
      htotalEmpty, htotalInner⟩
  refine
    ⟨κEmpty × κInner,
      (fun ew => (emptyCaseSet ew).product (innerCaseSet ew)),
      (fun ew m => (emptyCaseOf ew m, innerCaseOf ew m)),
      (fun ew c => emptyRowBound ew c.1),
      (fun ew c => emptyRelaxedBudget ew c.1),
      (fun ew c => innerRowBound ew c.2),
      (fun ew c => innerRelaxedBudget ew c.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
  · intro ew hew m hm
    exact Finset.mem_product.mpr
      ⟨hcoverEmpty ew hew m hm, hcoverInner ew hew m hm⟩
  · intro ew hew m hm
    simpa using hpointEmpty ew hew m hm
  · intro ew hew m hm
    simpa using hpointInner ew hew m hm
  · intro ew hew c hc
    exact hrelaxEmpty ew hew c.1 (Finset.mem_product.mp hc).1
  · intro ew hew c hc
    exact hrelaxInner ew hew c.2 (Finset.mem_product.mp hc).2
  · intro ew hew c hc
    exact hnonnegEmpty ew hew c.1 (Finset.mem_product.mp hc).1
  · intro ew hew c hc
    exact hnonnegInner ew hew c.2 (Finset.mem_product.mp hc).2
  · exact
      @sum_finiteSupportExplicitCaseBudgetTotal_product_fst_le
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset)
        κEmpty κInner
        (doubledBoxOriginIncidentEdges n)
        (fun ew => Ω.filter (fun m => m ew ≠ 0))
        emptyCaseOf innerCaseOf emptyCaseSet innerCaseSet
        emptyRelaxedBudget _ hcoverEmpty hcoverInner htotalEmpty
  · exact
      @sum_finiteSupportExplicitCaseBudgetTotal_product_snd_le
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset)
        κEmpty κInner
        (doubledBoxOriginIncidentEdges n)
        (fun ew => Ω.filter (fun m => m ew ≠ 0))
        emptyCaseOf innerCaseOf emptyCaseSet innerCaseSet
        innerRelaxedBudget _ hcoverEmpty hcoverInner htotalInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
      innerRowBound, innerRelaxedBudget, hcover, hpointEmpty, hpointInner,
      hrelaxEmpty, hrelaxInner, _hnonnegEmpty, _hnonnegInner, htotalEmpty,
      htotalInner⟩
  exact
    ⟨κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget, innerRowBound,
      innerRelaxedBudget, hcover, hpointEmpty, hpointInner, hrelaxEmpty,
      hrelaxInner, htotalEmpty, htotalInner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ} (hβ : 0 ≤ β)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n := by
  refine ⟨?_, ?_⟩
  · intro v hvwedge hlt hypos e0 hedge Ω
    rcases htable v hvwedge hlt hypos e0 hedge Ω with
      ⟨κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
        _innerRowBound, _innerRelaxedBudget, hcover, hpointEmpty,
        _hpointInner, hrelaxEmpty, _hrelaxInner, htotalEmpty,
        _htotalInner⟩
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
      simpa [w] using
        boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
    have hheight :
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
      simpa [w] using
        boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos
    have hadj :
        (FK.boxGraph 3 (2 * n)).Adj
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
      simpa [w] using
        boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
          (by omega : n ≤ 2 * n) v hvwedge hlt hypos
    rcases
        doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
          (n := n) (v := v) (w := w) hvwedge hwwedge hheight hadj with
      ⟨_edge, _hedge, hov, _how, _hvw⟩
    exact
      finset_sum_le_of_doubledBoxOriginIncidentEdgeWitnessFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        (n := n) (κ := κ) Ω
        (fun m =>
          doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
        caseOf caseSet emptyRowBound emptyRelaxedBudget
        (by
          intro m hm hnot
          exact
            doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
              (β := β) (n := n) (v := v)
              (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m hov hnot)
        (by
          intro m _hm
          exact
            doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_nonneg
              (β := β) (n := n) (v := v)
              (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              hβ e0 m)
        hcover hpointEmpty hrelaxEmpty htotalEmpty
  · intro v hvwedge hlt hypos e0 hedge Ω
    rcases htable v hvwedge hlt hypos e0 hedge Ω with
      ⟨κ, caseSet, caseOf, _emptyRowBound, _emptyRelaxedBudget,
        innerRowBound, innerRelaxedBudget, hcover, _hpointEmpty,
        hpointInner, _hrelaxEmpty, hrelaxInner, _htotalEmpty,
        htotalInner⟩
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
      simpa [w] using
        boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
    have hheight :
        boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
      simpa [w] using
        boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos
    have hadj :
        (FK.boxGraph 3 (2 * n)).Adj
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w)
          (FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v) := by
      simpa [w] using
        boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
          (by omega : n ≤ 2 * n) v hvwedge hlt hypos
    rcases
        doubledBoxOriginToInnerEndpoint_edgeData_of_orderedWedge_lowerDoubledAdj
          (n := n) (v := v) (w := w) hvwedge hwwedge hheight hadj with
      ⟨_edge, _hedge, _hov, how, _hvw⟩
    have howPred :
        IsingFK.boxOrigin 3 (2 * n) ≠
          FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) := by
      simpa [w] using how
    exact
      finset_sum_le_of_doubledBoxOriginIncidentEdgeWitnessFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        (n := n) (κ := κ) Ω
        (fun m =>
          doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m)
        caseOf caseSet innerRowBound innerRelaxedBudget
        (by
          intro m hm hnot
          exact
            doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_zero_of_not_originTouchesEdgeSupport
              (β := β) (n := n) (v := v)
              (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              e0 m howPred hnot)
        (by
          intro m _hm
          exact
            doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_nonneg
              (β := β) (n := n) (v := v)
              (w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
              hβ e0 m)
        hcover hpointInner hrelaxInner htotalInner

end Exact3D
end StatMech
