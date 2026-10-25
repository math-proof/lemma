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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part142
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ} (hn : 0 < n)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, hcoverEmpty, hcoverInner, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, htotalEmpty, htotalInner⟩
  refine
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, hcoverEmpty, hcoverInner, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, ?_, ?_⟩
  · exact
      doubledBoxOriginIncidentEdges_sum_le_of_forall_le_div_six
        (n := n) hn
        (F := fun ew =>
          finiteSupportExplicitCaseBudgetTotal
            (Ω.filter
              (fun m => doubledBoxOriginIncidentOwner n m = some ew))
            (emptyCaseOf ew) (emptyCaseSet ew) (emptyRelaxedBudget ew))
        (target := doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v)
        htotalEmpty
  · exact
      doubledBoxOriginIncidentEdges_sum_le_of_forall_le_div_six
        (n := n) hn
        (F := fun ew =>
          finiteSupportExplicitCaseBudgetTotal
            (Ω.filter
              (fun m => doubledBoxOriginIncidentOwner n m = some ew))
            (innerCaseOf ew) (innerCaseSet ew) (innerRelaxedBudget ew))
        (target :=
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
        htotalInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, hcoverEmpty, hcoverInner, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, htotalEmpty, htotalInner⟩
  refine
    ⟨κEmpty × κInner,
      (fun ew => (emptyCaseSet ew).product (innerCaseSet ew)),
      (fun ew m => (emptyCaseOf ew m, innerCaseOf ew m)),
      (fun ew c => emptyRowBound ew c.1),
      (fun ew c => emptyRelaxedBudget ew c.1),
      (fun ew c => innerRowBound ew c.2),
      (fun ew c => innerRelaxedBudget ew c.2), ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
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
  · exact
      @sum_finiteSupportExplicitCaseBudgetTotal_product_fst_le
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset)
        κEmpty κInner
        (doubledBoxOriginIncidentEdges n)
        (fun ew =>
          Ω.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew))
        emptyCaseOf innerCaseOf emptyCaseSet innerCaseSet
        emptyRelaxedBudget _ hcoverEmpty hcoverInner htotalEmpty
  · exact
      @sum_finiteSupportExplicitCaseBudgetTotal_product_snd_le
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)
        (↥(FK.boxGraph 3 (2 * n)).edgeFinset)
        κEmpty κInner
        (doubledBoxOriginIncidentEdges n)
        (fun ew =>
          Ω.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew))
        emptyCaseOf innerCaseOf emptyCaseSet innerCaseSet
        innerRelaxedBudget _ hcoverEmpty hcoverInner htotalInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, hcoverEmpty, hcoverInner, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, hnonnegEmpty, hnonnegInner,
      htotalEmpty, htotalInner⟩
  refine
    ⟨κEmpty, κInner, emptyCaseSet, emptyCaseOf, emptyRowBound,
      emptyRelaxedBudget, innerCaseSet, innerCaseOf, innerRowBound,
      innerRelaxedBudget, ?_, ?_, ?_, ?_, hrelaxEmpty, hrelaxInner, ?_,
      ?_⟩
  · intro ew hew m hm
    exact hcoverEmpty ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hcoverInner ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hpointEmpty ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hpointInner ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · exact
      (sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_multiplicityFilters_of_nonneg
        (n := n) Ω emptyCaseOf emptyCaseSet emptyRelaxedBudget
        hcoverEmpty hnonnegEmpty).trans htotalEmpty
  · exact
      (sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_multiplicityFilters_of_nonneg
        (n := n) Ω innerCaseOf innerCaseSet innerRelaxedBudget
        hcoverInner hnonnegInner).trans htotalInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
      innerRowBound, innerRelaxedBudget, hcover, hpointEmpty, hpointInner,
      hrelaxEmpty, hrelaxInner, hnonnegEmpty, hnonnegInner, htotalEmpty,
      htotalInner⟩
  refine
    ⟨κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
      innerRowBound, innerRelaxedBudget, ?_, ?_, ?_, hrelaxEmpty,
      hrelaxInner, ?_, ?_⟩
  · intro ew hew m hm
    exact hcover ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hpointEmpty ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · intro ew hew m hm
    exact hpointInner ew hew m <|
      doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
        (n := n) Ω ew hm
  · exact
      (sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_multiplicityFilters_of_nonneg
        (n := n) Ω caseOf caseSet emptyRelaxedBudget hcover
        hnonnegEmpty).trans htotalEmpty
  · exact
      (sum_finiteSupportExplicitCaseBudgetTotal_doubledBoxOriginIncidentOwnerFilters_le_multiplicityFilters_of_nonneg
        (n := n) Ω caseOf caseSet innerRelaxedBudget hcover
        hnonnegInner).trans htotalInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
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
      finset_sum_le_of_doubledBoxOriginIncidentEdgeOwnerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
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
      finset_sum_le_of_doubledBoxOriginIncidentEdgeOwnerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
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
        hcover hpointInner hrelaxInner htotalInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentEdgeWitnessNonnegativeRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundAt_of_selectedCopyEmptyFiniteCutoffExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, caseBudget, hcover, hpoint, htotal⟩
  refine ⟨κ, caseOf, caseBudget, hpoint, ?_⟩
  exact
    finiteSupportCaseBudgetTotal_le_of_finiteSupportExplicitCaseBudgetTotal_le
      Ω caseOf caseSet caseBudget hcover htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundAt_of_selectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, caseBudget, hcover, hpoint, htotal⟩
  refine ⟨κ, caseOf, caseBudget, hpoint, ?_⟩
  exact
    finiteSupportCaseBudgetTotal_le_of_finiteSupportExplicitCaseBudgetTotal_le
      Ω caseOf caseSet caseBudget hcover htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableBoundsAt_of_selectedCopyFiniteCutoffExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundAt_of_selectedCopyEmptyFiniteCutoffExplicitCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundAt_of_selectedCopyInnerPairFiniteCutoffExplicitCaseTableBoundAt
      htable.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundAt_of_selectedCopyEmptyFiniteCutoffCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseOf, caseBudget, hpoint, htotal⟩
  refine ⟨fun m => caseBudget (caseOf m), hpoint, ?_⟩
  calc
    (∑ m ∈ Ω, caseBudget (caseOf m)) =
        finiteSupportCaseBudgetTotal Ω caseOf caseBudget := by
      exact finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω caseOf
        caseBudget
    _ ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundAt_of_selectedCopyInnerPairFiniteCutoffCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseOf, caseBudget, hpoint, htotal⟩
  refine ⟨fun m => caseBudget (caseOf m), hpoint, ?_⟩
  calc
    (∑ m ∈ Ω, caseBudget (caseOf m)) =
        finiteSupportCaseBudgetTotal Ω caseOf caseBudget := by
      exact finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω caseOf
        caseBudget
    _ ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantBoundsAt_of_selectedCopyFiniteCutoffCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundAt_of_selectedCopyEmptyFiniteCutoffCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundAt_of_selectedCopyInnerPairFiniteCutoffCaseTableBoundAt
      htable.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt_of_selectedCopyEmptyFiniteCutoffMajorantBoundAt
    {β : ℝ} {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases hmajor v hvwedge hlt hypos e0 hedge Ω with
    ⟨budget, hpoint, hbudget⟩
  exact (Finset.sum_le_sum hpoint).trans hbudget

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt_of_selectedCopyInnerPairFiniteCutoffMajorantBoundAt
    {β : ℝ} {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases hmajor v hvwedge hlt hypos e0 hedge Ω with
    ⟨budget, hpoint, hbudget⟩
  exact (Finset.sum_le_sum hpoint).trans hbudget

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffMajorantBoundsAt
    {β : ℝ} {n : ℕ}
    (hmajor :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt_of_selectedCopyEmptyFiniteCutoffMajorantBoundAt
      hmajor.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt_of_selectedCopyInnerPairFiniteCutoffMajorantBoundAt
      hmajor.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundAt_of_selectedCopyEmptyFiniteCutoffBoundAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hfinite :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_summable_of_sourceSectorResidualMomentEmptyBranchSummand_summable
        (β := β) (n := n) (v := v) (w := w) hβ e0
        (doubledBoxSourceSectorResidualMomentEmptyBranchSummand_summable_of_nonneg_beta
          hβ.le n v w e0)
  · intro Ω
    exact hfinite v hvwedge hlt hypos e0 hedge Ω

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundAt_of_selectedCopyInnerPairFiniteCutoffBoundAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hfinite :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  refine tsum_le_of_all_finset_sum_le ?_ ?_
  · exact
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_summable_of_sourceSectorResidualMomentInnerPairBranchSummand_summable
        (β := β) (n := n) (v := v) (w := w) hβ e0
        (doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_summable_of_nonneg_beta
          hβ.le n v w e0)
  · intro Ω
    exact hfinite v hvwedge hlt hypos e0 hedge Ω

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAt_of_selectedCopyFiniteCutoffBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (hfinite :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundAt_of_selectedCopyEmptyFiniteCutoffBoundAt
      hβ hfinite.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundAt_of_selectedCopyInnerPairFiniteCutoffBoundAt
      hβ hfinite.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt_of_selectedCopyEmptyBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hsel := hselected v hvwedge hlt hypos e0 hedge
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentEmptyBranchSummand β n v w e0 m) =
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          β *
            doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
              e0 m := by
      refine tsum_congr ?_
      intro m
      exact
        (beta_mul_doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand_eq_sourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m).symm
    _ =
        β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v w
            e0 m) := by
      rw [tsum_mul_left]
    _ ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
      exact mul_le_mul_of_nonneg_left hsel hβ

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt_of_selectedCopyInnerPairBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hsel := hselected v hvwedge hlt hypos e0 hedge
  calc
    (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
        doubledBoxSourceSectorResidualMomentInnerPairBranchSummand β n v w e0
          m) =
        ∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          β *
            doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n
              v w e0 m := by
      refine tsum_congr ?_
      intro m
      exact
        (beta_mul_doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand_eq_sourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m).symm
    _ =
        β * (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
          doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
            w e0 m) := by
      rw [tsum_mul_left]
    _ ≤
        β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
      exact mul_le_mul_of_nonneg_left hsel hβ

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_selectedCopyBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundAt_of_selectedCopyEmptyBoundAt
      hβ hselected.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundAt_of_selectedCopyInnerPairBoundAt
      hβ hselected.2⟩

end Exact3D
end StatMech
