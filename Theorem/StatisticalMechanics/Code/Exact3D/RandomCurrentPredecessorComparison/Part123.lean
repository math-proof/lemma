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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part115
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityIndependentBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityIndependentBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κEmptyIn, κEmptyOutside, κInnerIn, κInnerOutside, emptyInCaseSet,
      emptyInCaseOf, emptyInRowBound, emptyInRelaxedBudget,
      emptyOutsideCaseSet, emptyOutsideCaseOf, emptyOutsideRowBound,
      emptyOutsideRelaxedBudget, innerInCaseSet, innerInCaseOf,
      innerInRowBound, innerInRelaxedBudget, innerOutsideCaseSet,
      innerOutsideCaseOf, innerOutsideRowBound, innerOutsideRelaxedBudget,
      hcoverEmptyIn, hcoverEmptyOutside, hcoverInnerIn, hcoverInnerOutside,
      hpointEmptyIn, hpointEmptyOutside, hpointInnerIn, hpointInnerOutside,
      hrelaxEmptyIn, hrelaxEmptyOutside, hrelaxInnerIn, hrelaxInnerOutside,
      hnonnegEmpty, hnonnegInner, htotalEmpty, htotalInner⟩
  refine
    ⟨(κEmptyIn × κEmptyOutside) × (κInnerIn × κInnerOutside),
      (fun ew =>
        ((emptyInCaseSet ew).product (emptyOutsideCaseSet ew)).product
          ((innerInCaseSet ew).product (innerOutsideCaseSet ew))),
      (fun ew m =>
        ((emptyInCaseOf ew m, emptyOutsideCaseOf ew m),
          (innerInCaseOf ew m, innerOutsideCaseOf ew m))),
      (fun ew c => emptyInRowBound ew c.1.1),
      (fun ew c => emptyOutsideRowBound ew c.1.2),
      (fun ew c => innerInRowBound ew c.2.1),
      (fun ew c => innerOutsideRowBound ew c.2.2),
      (fun ew c => emptyInRelaxedBudget ew c.1.1),
      (fun ew c => emptyOutsideRelaxedBudget ew c.1.2),
      (fun ew c => innerInRelaxedBudget ew c.2.1),
      (fun ew c => innerOutsideRelaxedBudget ew c.2.2),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ew hew m hm
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
          ⟨hcoverEmptyIn ew hew m hm, hcoverEmptyOutside ew hew m hm⟩,
        Finset.mem_product.mpr
          ⟨hcoverInnerIn ew hew m hm, hcoverInnerOutside ew hew m hm⟩⟩
  · intro ew hew m hm
    exact hpointEmptyIn ew hew m hm
  · intro ew hew m hm
    exact hpointEmptyOutside ew hew m hm
  · intro ew hew m hm
    exact hpointInnerIn ew hew m hm
  · intro ew hew m hm
    exact hpointInnerOutside ew hew m hm
  · intro ew hew c hc
    exact hrelaxEmptyIn ew hew c.1.1
      (Finset.mem_product.mp (Finset.mem_product.mp hc).1).1
  · intro ew hew c hc
    exact hrelaxEmptyOutside ew hew c.1.2
      (Finset.mem_product.mp (Finset.mem_product.mp hc).1).2
  · intro ew hew c hc
    exact hrelaxInnerIn ew hew c.2.1
      (Finset.mem_product.mp (Finset.mem_product.mp hc).2).1
  · intro ew hew c hc
    exact hrelaxInnerOutside ew hew c.2.2
      (Finset.mem_product.mp (Finset.mem_product.mp hc).2).2
  · intro ew hew c hc
    exact
      hnonnegEmpty ew hew c.1.1
        (Finset.mem_product.mp (Finset.mem_product.mp hc).1).1 c.1.2
        (Finset.mem_product.mp (Finset.mem_product.mp hc).1).2
  · intro ew hew c hc
    exact
      hnonnegInner ew hew c.2.1
        (Finset.mem_product.mp (Finset.mem_product.mp hc).2).1 c.2.2
        (Finset.mem_product.mp (Finset.mem_product.mp hc).2).2
  · intro ew hew
    let Ωew :=
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)
    have hcoverEmptyPair :
        ∀ m ∈ Ωew,
          (emptyInCaseOf ew m, emptyOutsideCaseOf ew m) ∈
            (emptyInCaseSet ew).product (emptyOutsideCaseSet ew) := by
      intro m hm
      exact Finset.mem_product.mpr
        ⟨hcoverEmptyIn ew hew m (by simpa [Ωew] using hm),
          hcoverEmptyOutside ew hew m (by simpa [Ωew] using hm)⟩
    have hcoverInnerPair :
        ∀ m ∈ Ωew,
          (innerInCaseOf ew m, innerOutsideCaseOf ew m) ∈
            (innerInCaseSet ew).product (innerOutsideCaseSet ew) := by
      intro m hm
      exact Finset.mem_product.mpr
        ⟨hcoverInnerIn ew hew m (by simpa [Ωew] using hm),
          hcoverInnerOutside ew hew m (by simpa [Ωew] using hm)⟩
    have hcoverEmptyIn' :
        ∀ m ∈ Ωew, emptyInCaseOf ew m ∈ emptyInCaseSet ew := by
      intro m hm
      exact hcoverEmptyIn ew hew m (by simpa [Ωew] using hm)
    have hcoverEmptyOutside' :
        ∀ m ∈ Ωew,
          emptyOutsideCaseOf ew m ∈ emptyOutsideCaseSet ew := by
      intro m hm
      exact hcoverEmptyOutside ew hew m (by simpa [Ωew] using hm)
    calc
      finiteSupportExplicitCaseBudgetTotal Ωew
          (fun m =>
            ((emptyInCaseOf ew m, emptyOutsideCaseOf ew m),
              (innerInCaseOf ew m, innerOutsideCaseOf ew m)))
          (((emptyInCaseSet ew).product (emptyOutsideCaseSet ew)).product
            ((innerInCaseSet ew).product (innerOutsideCaseSet ew)))
          (fun c =>
            emptyInRelaxedBudget ew c.1.1 +
              emptyOutsideRelaxedBudget ew c.1.2) =
        finiteSupportExplicitCaseBudgetTotal Ωew
          (fun m => (emptyInCaseOf ew m, emptyOutsideCaseOf ew m))
          ((emptyInCaseSet ew).product (emptyOutsideCaseSet ew))
          (fun c =>
            emptyInRelaxedBudget ew c.1 +
              emptyOutsideRelaxedBudget ew c.2) := by
          exact
            finiteSupportExplicitCaseBudgetTotal_product_fst_eq Ωew
              (fun m => (emptyInCaseOf ew m, emptyOutsideCaseOf ew m))
              (fun m => (innerInCaseOf ew m, innerOutsideCaseOf ew m))
              ((emptyInCaseSet ew).product (emptyOutsideCaseSet ew))
              ((innerInCaseSet ew).product (innerOutsideCaseSet ew))
              (fun c =>
                emptyInRelaxedBudget ew c.1 +
                  emptyOutsideRelaxedBudget ew c.2)
              hcoverEmptyPair hcoverInnerPair
      _ =
        finiteSupportExplicitCaseBudgetTotal Ωew (emptyInCaseOf ew)
            (emptyInCaseSet ew) (emptyInRelaxedBudget ew) +
          finiteSupportExplicitCaseBudgetTotal Ωew (emptyOutsideCaseOf ew)
            (emptyOutsideCaseSet ew) (emptyOutsideRelaxedBudget ew) := by
          exact
            finiteSupportExplicitCaseBudgetTotal_product_add_eq Ωew
              (emptyInCaseOf ew) (emptyOutsideCaseOf ew)
              (emptyInCaseSet ew) (emptyOutsideCaseSet ew)
              (emptyInRelaxedBudget ew) (emptyOutsideRelaxedBudget ew)
              hcoverEmptyIn' hcoverEmptyOutside'
      _ ≤ (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
          6 := by
          exact htotalEmpty ew hew
  · intro ew hew
    let Ωew :=
      (Ω.filter
        (doubledBoxIncrementedFullSourceActive n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
        (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0)
    have hcoverEmptyPair :
        ∀ m ∈ Ωew,
          (emptyInCaseOf ew m, emptyOutsideCaseOf ew m) ∈
            (emptyInCaseSet ew).product (emptyOutsideCaseSet ew) := by
      intro m hm
      exact Finset.mem_product.mpr
        ⟨hcoverEmptyIn ew hew m (by simpa [Ωew] using hm),
          hcoverEmptyOutside ew hew m (by simpa [Ωew] using hm)⟩
    have hcoverInnerPair :
        ∀ m ∈ Ωew,
          (innerInCaseOf ew m, innerOutsideCaseOf ew m) ∈
            (innerInCaseSet ew).product (innerOutsideCaseSet ew) := by
      intro m hm
      exact Finset.mem_product.mpr
        ⟨hcoverInnerIn ew hew m (by simpa [Ωew] using hm),
          hcoverInnerOutside ew hew m (by simpa [Ωew] using hm)⟩
    have hcoverInnerIn' :
        ∀ m ∈ Ωew, innerInCaseOf ew m ∈ innerInCaseSet ew := by
      intro m hm
      exact hcoverInnerIn ew hew m (by simpa [Ωew] using hm)
    have hcoverInnerOutside' :
        ∀ m ∈ Ωew,
          innerOutsideCaseOf ew m ∈ innerOutsideCaseSet ew := by
      intro m hm
      exact hcoverInnerOutside ew hew m (by simpa [Ωew] using hm)
    calc
      finiteSupportExplicitCaseBudgetTotal Ωew
          (fun m =>
            ((emptyInCaseOf ew m, emptyOutsideCaseOf ew m),
              (innerInCaseOf ew m, innerOutsideCaseOf ew m)))
          (((emptyInCaseSet ew).product (emptyOutsideCaseSet ew)).product
            ((innerInCaseSet ew).product (innerOutsideCaseSet ew)))
          (fun c =>
            innerInRelaxedBudget ew c.2.1 +
              innerOutsideRelaxedBudget ew c.2.2) =
        finiteSupportExplicitCaseBudgetTotal Ωew
          (fun m => (innerInCaseOf ew m, innerOutsideCaseOf ew m))
          ((innerInCaseSet ew).product (innerOutsideCaseSet ew))
          (fun c =>
            innerInRelaxedBudget ew c.1 +
              innerOutsideRelaxedBudget ew c.2) := by
          exact
            finiteSupportExplicitCaseBudgetTotal_product_snd_eq Ωew
              (fun m => (emptyInCaseOf ew m, emptyOutsideCaseOf ew m))
              (fun m => (innerInCaseOf ew m, innerOutsideCaseOf ew m))
              ((emptyInCaseSet ew).product (emptyOutsideCaseSet ew))
              ((innerInCaseSet ew).product (innerOutsideCaseSet ew))
              (fun c =>
                innerInRelaxedBudget ew c.1 +
                  innerOutsideRelaxedBudget ew c.2)
              hcoverEmptyPair hcoverInnerPair
      _ =
        finiteSupportExplicitCaseBudgetTotal Ωew (innerInCaseOf ew)
            (innerInCaseSet ew) (innerInRelaxedBudget ew) +
          finiteSupportExplicitCaseBudgetTotal Ωew (innerOutsideCaseOf ew)
            (innerOutsideCaseSet ew) (innerOutsideRelaxedBudget ew) := by
          exact
            finiteSupportExplicitCaseBudgetTotal_product_add_eq Ωew
              (innerInCaseOf ew) (innerOutsideCaseOf ew)
              (innerInCaseSet ew) (innerOutsideCaseSet ew)
              (innerInRelaxedBudget ew) (innerOutsideRelaxedBudget ew)
              hcoverInnerIn' hcoverInnerOutside'
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
              (doubledBoxInnerPairSource n v
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) /
            6 := by
          exact htotalInner ew hew

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseInOutSelectedCopySixthRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseInOutSelectedCopySixthRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBoundEmptyIn, rowBoundEmptyOutside,
      rowBoundInnerIn, rowBoundInnerOutside, relaxedBudgetEmptyIn,
      relaxedBudgetEmptyOutside, relaxedBudgetInnerIn,
      relaxedBudgetInnerOutside, hcover, hpointEmptyIn, hpointEmptyOutside,
      hpointInnerIn, hpointInnerOutside, hrelaxEmptyIn,
      hrelaxEmptyOutside, hrelaxInnerIn, hrelaxInnerOutside, hnonnegEmpty,
      hnonnegInner, htotalEmpty, htotalInner⟩
  refine
    ⟨κ, caseSet, caseOf, rowBoundEmptyIn, rowBoundEmptyOutside,
      rowBoundInnerIn, rowBoundInnerOutside, relaxedBudgetEmptyIn,
      relaxedBudgetEmptyOutside, relaxedBudgetInnerIn,
      relaxedBudgetInnerOutside, ?_, ?_, ?_, ?_, ?_, hrelaxEmptyIn,
      hrelaxEmptyOutside, hrelaxInnerIn, hrelaxInnerOutside, ?_, ?_⟩
  · intro ew hew
    exact
      forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (hcover ew hew)
  · intro ew hew
    exact
      forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (hpointEmptyIn ew hew)
  · intro ew hew
    exact
      forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (hpointEmptyOutside ew hew)
  · intro ew hew
    exact
      forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (hpointInnerIn ew hew)
  · intro ew hew
    exact
      forall_activeOriginIncidentOwnerRows_of_forall_updateSelectedEdgeMultiplicityRows_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (hpointInnerOutside ew hew)
  · intro ew hew
    exact
      (finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentOwnerFilter_le_updateSelectedEdgeMultiplicityFilter_of_nonneg
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (caseOf ew) (caseSet ew)
        (fun c =>
          relaxedBudgetEmptyIn ew c + relaxedBudgetEmptyOutside ew c)
        (hcover ew hew) (hnonnegEmpty ew hew)).trans
        (htotalEmpty ew hew)
  · intro ew hew
    exact
      (finiteSupportExplicitCaseBudgetTotal_strictSectorYActiveOriginIncidentOwnerFilter_le_updateSelectedEdgeMultiplicityFilter_of_nonneg
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
        (by simpa [w] using hedge) Ω (caseOf ew) (caseSet ew)
        (fun c =>
          relaxedBudgetInnerIn ew c + relaxedBudgetInnerOutside ew c)
        (hcover ew hew) (hnonnegInner ew hew)).trans
        (htotalInner ew hew)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseInOutSelectedCopySixthRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseInOutSelectedCopySixthRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBoundEmptyIn, rowBoundEmptyOutside,
      rowBoundInnerIn, rowBoundInnerOutside, relaxedBudgetEmptyIn,
      relaxedBudgetEmptyOutside, relaxedBudgetInnerIn,
      relaxedBudgetInnerOutside, hcover, hpointEmptyIn, hpointEmptyOutside,
      hpointInnerIn, hpointInnerOutside, hrelaxEmptyIn,
      hrelaxEmptyOutside, hrelaxInnerIn, hrelaxInnerOutside, htotalEmpty,
      htotalInner⟩
  refine
    ⟨κ, caseSet, caseOf,
      (fun ew c => rowBoundEmptyIn ew c + rowBoundEmptyOutside ew c),
      (fun ew c => rowBoundInnerIn ew c + rowBoundInnerOutside ew c),
      (fun ew c => relaxedBudgetEmptyIn ew c +
        relaxedBudgetEmptyOutside ew c),
      (fun ew c => relaxedBudgetInnerIn ew c +
        relaxedBudgetInnerOutside ew c),
      hcover, ?_, ?_, ?_, ?_, htotalEmpty, htotalInner⟩
  · intro ew hew m hm
    rw [
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_inCurrent_add_beta_mul_outsideCurrent]
    exact
      add_le_add (hpointEmptyIn ew hew m hm)
        (hpointEmptyOutside ew hew m hm)
  · intro ew hew m hm
    rw [
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_inCurrent_add_beta_mul_outsideCurrent]
    exact
      add_le_add (hpointInnerIn ew hew m hm)
        (hpointInnerOutside ew hew m hm)
  · intro ew hew c hc
    exact
      add_le_add (hrelaxEmptyIn ew hew c hc)
        (hrelaxEmptyOutside ew hew c hc)
  · intro ew hew c hc
    exact
      add_le_add (hrelaxInnerIn ew hew c hc)
        (hrelaxInnerOutside ew hew c hc)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBoundEmpty, rowBoundInner,
      relaxedBudgetEmpty, relaxedBudgetInner, hcover, hpointEmpty,
      hpointInner, hrelaxEmpty, hrelaxInner, htotalEmpty, htotalInner⟩
  refine
    ⟨κ, caseSet, caseOf,
      (fun ew c => rowBoundEmpty ew c + rowBoundInner ew c),
      (fun ew c => relaxedBudgetEmpty ew c + relaxedBudgetInner ew c),
      hcover, ?_, ?_, ?_⟩
  · intro ew hew m hm
    change
      doubledBoxSwitchedSourceSectorResidualMomentBranchSummand β n v w e0 m ≤
        rowBoundEmpty ew (caseOf ew m) + rowBoundInner ew (caseOf ew m)
    rw [doubledBoxSwitchedSourceSectorResidualMomentBranchSummand_eq_empty_add_inner]
    exact add_le_add (hpointEmpty ew hew m hm) (hpointInner ew hew m hm)
  · intro ew hew c hc
    exact add_le_add (hrelaxEmpty ew hew c hc) (hrelaxInner ew hew c hc)
  · intro ew hew
    let Ωew :=
      (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
        (fun m => doubledBoxOriginIncidentOwner n m = some ew)
    calc
      finiteSupportExplicitCaseBudgetTotal Ωew (caseOf ew) (caseSet ew)
          (fun c => relaxedBudgetEmpty ew c + relaxedBudgetInner ew c)
          =
        finiteSupportExplicitCaseBudgetTotal Ωew (caseOf ew) (caseSet ew)
            (relaxedBudgetEmpty ew) +
          finiteSupportExplicitCaseBudgetTotal Ωew (caseOf ew) (caseSet ew)
            (relaxedBudgetInner ew) := by
          rw [finiteSupportExplicitCaseBudgetTotal_add]
      _ ≤
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 +
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) / 6 := by
          exact add_le_add (htotalEmpty ew hew) (htotalInner ew hew)
      _ =
        (β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w))) / 6 := by
          ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ} (hn : 0 < n)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBound, relaxedBudget, hcover, hpoint, hrelax,
      hperOwner⟩
  refine
    ⟨κ, caseSet, caseOf, rowBound, relaxedBudget, hcover, hpoint, hrelax,
      ?_⟩
  exact
    doubledBoxOriginIncidentEdges_sum_le_of_forall_le_div_six
      (n := n) hn
      (F := fun ew =>
        finiteSupportExplicitCaseBudgetTotal
          ((Ω.filter
            (doubledBoxIncrementedFullSourceActive n w e0)).filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew))
          (caseOf ew) (caseSet ew) (relaxedBudget ew))
      (target :=
        β *
          (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)))
      hperOwner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let active :=
    doubledBoxIncrementedFullSourceActive n w e0
  let F :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      (((edgeCopySourceSector (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (Function.update m e0 (m e0 + 1))).card : ℕ) : ℝ) *
        doubledBoxResidualMomentBranchSummand β n v w e0 m
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBound, relaxedBudget, hcover, hpoint, hrelax,
      htotal⟩
  refine
    finset_sum_le_of_ownerFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
      (Ω.filter active) (doubledBoxOriginIncidentEdges n)
      (doubledBoxOriginIncidentOwner n) F caseOf caseSet rowBound
      relaxedBudget ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm howner_none
    have hactive : doubledBoxIncrementedFullSourceActive n w e0 m := by
      simpa [active] using (Finset.mem_filter.mp hm).2
    have htouch : doubledBoxOriginTouchesEdgeSupport n m :=
      doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
        (by simpa [w] using hedge) (by simpa [w] using hactive)
    exact False.elim
      (((doubledBoxOriginIncidentOwner_eq_none_iff_not_originTouchesEdgeSupport
        (n := n) (m := m)).1 howner_none) htouch)
  · intro m _hm ew howner
    exact
      (doubledBoxOriginIncidentOwner_spec_of_eq_some
        (n := n) (m := m) (e := ew) howner).1
  · intro ew hew m hm
    simpa [active, w] using hcover ew hew m hm
  · intro ew hew m hm
    simpa [active, w, F] using hpoint ew hew m hm
  · intro ew hew c hc
    exact hrelax ew hew c hc
  · simpa [active, w] using htotal

end Exact3D
end StatMech
