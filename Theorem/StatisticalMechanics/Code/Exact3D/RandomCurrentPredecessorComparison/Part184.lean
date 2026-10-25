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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part176
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_totalPairCardExpectationJSplitPositiveSubcritical
    (hcert :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYTotalPairCardExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcert β hβpos hβc) fun n hn =>
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_totalPairCardExpectationJSplitAt
      hβpos hn


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt_of_rows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgePredecessorExpectationJRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt
      β n := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hvwedge hlt
    let p :
        {u : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n u ∧
            ((u : Lattice.Site 3) (1 : Fin 3)) <
              ((u : Lattice.Site 3) (2 : Fin 3))} :=
      ⟨v, hvwedge, hlt⟩
    exact T.soundStrictZ p (hrows (T.classifyStrictZ p) (T.coversStrictZ p))
  · intro v hvwedge hheight hnotlt
    let p :
        {u : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n u ∧
            boxVertTransverseHeight3 u ≠ 0 ∧
              ¬ ((u : Lattice.Site 3) (1 : Fin 3)) <
                ((u : Lattice.Site 3) (2 : Fin 3))} :=
      ⟨v, hvwedge, hheight, hnotlt⟩
    exact T.soundDiagY p (hrows (T.classifyDiagY p) (T.coversDiagY p))
  · intro v hvwedge hlt hypos
    let p :
        {u : FK.boxVerts 3 n //
          boxVertPositiveXFaceOrderedWedge3 n u ∧
            ((u : Lattice.Site 3) (1 : Fin 3)) <
              ((u : Lattice.Site 3) (2 : Fin 3)) ∧
                0 < ((u : Lattice.Site 3) (1 : Fin 3))} :=
      ⟨v, hvwedge, hlt, hypos⟩
    exact T.soundStrictY p (hrows (T.classifyStrictY p) (T.coversStrictY p))


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical_of_local
    (hstrictZJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
    (hdiagYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical := by
  intro β _hβpos _hβc
  exact Filter.Eventually.of_forall fun n => by
    refine ⟨?_, ?_, ?_⟩
    · intro v hvwedge hlt
      exact hstrictZJ hvwedge hlt
    · intro v hvwedge hheight hnotlt
      exact hdiagYJ hvwedge hheight hnotlt
    · intro v hvwedge hlt hypos
      exact hstrictYJ hvwedge hlt hypos


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_predecessorCasesAt
    {β : ℝ} {n : ℕ}
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n := by
  rcases hcases with ⟨hstrictZJ, hdiagYJ, hstrictYJ⟩
  intro v w hvwedge hwwedge hheight hadj
  have hcase :=
    boxVertPositiveXFaceOrderedWedge3_lowerDoubledAdj_hasCoords3_yOrZ
      hvwedge hwwedge hheight hadj
  rcases hcase with hpredY | hpredZ
  · by_cases hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3))
    · have hy_pos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)) := by
        rcases hpredY with ⟨_hw0, hw1, _hw2⟩
        have hwwedge_y_nonneg := hwwedge.2.1
        rw [hw1] at hwwedge_y_nonneg
        omega
      have hcanon :
          boxVertHasCoords3
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hy_pos)
            (n : ℤ)
            (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
            ((v : Lattice.Site 3) (2 : Fin 3)) := by
        simp
      calc
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            ≤ Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hy_pos)) :=
          hstrictYJ v hvwedge hlt hy_pos
        _ = Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w) :=
          expectationJ_doubledBoxOriginToInnerEndpointSource_eq_of_boxVertHasCoords3
            hcanon hpredY
    · have hheight_ne : boxVertTransverseHeight3 v ≠ 0 := by
        omega
      have hcanon :
          boxVertHasCoords3
            (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hlt)
            (n : ℤ)
            (((v : Lattice.Site 3) (1 : Fin 3)) - 1)
            ((v : Lattice.Site 3) (2 : Fin 3)) := by
        simp
      calc
        Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            ≤ Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n
                (boxVertDiagonalPredecessor3 v hvwedge hheight_ne hlt)) :=
          hdiagYJ v hvwedge hheight_ne hlt
        _ = Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w) :=
          expectationJ_doubledBoxOriginToInnerEndpointSource_eq_of_boxVertHasCoords3
            hcanon hpredY
  · have hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)) := by
      rcases hpredZ with ⟨_hw0, hw1, hw2⟩
      have hwwedge_yz := hwwedge.2.2
      rw [hw1, hw2] at hwwedge_yz
      omega
    have hcanon :
        boxVertHasCoords3
          (boxVertStrictSectorPredecessor3 v hvwedge hlt)
          (n : ℤ)
          ((v : Lattice.Site 3) (1 : Fin 3))
          (((v : Lattice.Site 3) (2 : Fin 3)) - 1) := by
      simp
    calc
      Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          ≤ Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorPredecessor3 v hvwedge hlt)) :=
        hstrictZJ v hvwedge hlt
      _ = Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w) :=
        expectationJ_doubledBoxOriginToInnerEndpointSource_eq_of_boxVertHasCoords3
          hcanon hpredZ


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_predecessorRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgePredecessorExpectationJRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_predecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt_of_rows
      T hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_predecessorCasesPositiveSubcritical
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcases β hβpos hβc) fun n hn => by
    exact
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_predecessorCasesAt
        hn


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt_of_currentSumCasesAt
    {β : ℝ} {n : ℕ}
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt
      β n := by
  rcases hcases with ⟨hstrictZ, hdiagY, hstrictY⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v hvwedge hlt
    exact
      doubledBoxOriginToInnerEndpointExpectationJ_le_of_currentSum_le
        (hstrictZ v hvwedge hlt)
  · intro v hvwedge hheight hnotlt
    exact
      doubledBoxOriginToInnerEndpointExpectationJ_le_of_currentSum_le
        (hdiagY v hvwedge hheight hnotlt)
  · intro v hvwedge hlt hypos
    exact
      doubledBoxOriginToInnerEndpointExpectationJ_le_of_currentSum_le
        (hstrictY v hvwedge hlt hypos)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical_of_currentSumCasesPositiveSubcritical
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hcases β hβpos hβc) fun n hn => by
    exact
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt_of_currentSumCasesAt
        hn


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumPredecessorCasesAt
    {β : ℝ} {n : ℕ}
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_predecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt_of_currentSumCasesAt
      hcases)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgePredecessorCurrentSumRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumPredecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_rows
      T hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_currentSumPredecessorCasesPositiveSubcritical
    (hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_predecessorCasesPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesPositiveSubcritical_of_currentSumCasesPositiveSubcritical
      hcases)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorInjectionRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAt
        β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumPredecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorInjectionRows
      hβ T hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorInjectionRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorInjectionRowsAtPackage
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorInjectionRows
      hβ P.table P.rows_sound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_currentSumPredecessorCasesPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorInjectionRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T : OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumPredecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRows
      hβ T hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageRowsAtPackage
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumPredecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
      hβ P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageRowsPackage
    hβ
    (OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsAtPackage.toSourceSectorImageRowsAtPackage
      (β := β) P)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_currentSumPredecessorCasesPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
      hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageMultiplicityPreservingRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageMultiplicityPreservingRowsPositiveSubcritical
      hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeRelabelRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageEdgeRelabelRowsPositiveSubcritical
      hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageRowsPositiveSubcritical_of_sourceSectorImageEdgeVertexRelabelRowsPositiveSubcritical
      hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (hβ : 0 ≤ β)
    (T :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAt
        n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_currentSumPredecessorCasesAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
      hβ T hrows)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPackage
    {β : ℝ} {n : ℕ}
    (hβ : 0 ≤ β)
    (P :
      OrderedWedgePredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsAtPackage
        n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt
      β n := by
  letI := P.inst
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRows
      hβ P.table P.rows_sound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
    (hrows :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorEdgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJPositiveSubcritical_of_currentSumPredecessorCasesPositiveSubcritical
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorCurrentSumCasesPositiveSubcritical_of_edgeCopyCollapsedSourceSectorImageEdgeVertexRelabelEndpointMapRowsPositiveSubcritical
      hrows)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal_of_predecessorCases
    (hstrictZJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
    (hdiagYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal := by
  intro β n v w hvwedge hwwedge hheight hadj
  have hcases :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullPredecessorExpectationJCasesAt
        β n := by
    refine ⟨?_, ?_, ?_⟩
    · intro u huwedge hult
      exact hstrictZJ huwedge hult
    · intro u huwedge huheight hunotlt
      exact hdiagYJ huwedge huheight hunotlt
    · intro u huwedge hult hupos
      exact hstrictYJ huwedge hult hupos
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJAt_of_predecessorCasesAt
      (β := β) (n := n) hcases
      v w hvwedge hwwedge hheight hadj


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal_of_oneEdgeExpectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal := by
  intro β n v hvwedge hlt
  exact
    hJ hvwedge
      (boxVertStrictSectorPredecessor3_wedge v hvwedge hlt)
      (boxVertStrictSectorPredecessor3_height_lt v hvwedge hlt)
      (boxGraph_adj_boxVertInclLE_strictSectorPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hlt)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal_of_oneEdgeExpectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal := by
  intro β n v hvwedge hlt hypos
  exact
    hJ hvwedge
      (boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos)
      (boxVertStrictSectorYPredecessor3_height_lt v hvwedge hlt hypos)
      (boxGraph_adj_boxVertInclLE_strictSectorYPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hlt hypos)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal_of_oneEdgeExpectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentExpectationJLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal := by
  intro β n v hvwedge hheight hnotlt
  exact
    hJ hvwedge
      (boxVertDiagonalPredecessor3_wedge v hvwedge hheight hnotlt)
      (boxVertDiagonalPredecessor3_height_lt v hvwedge hheight hnotlt)
      (boxGraph_adj_boxVertInclLE_diagonalPredecessor3
        (by omega : n ≤ 2 * n) v hvwedge hheight hnotlt)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal_of_expectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal := by
  intro β hβpos n v hvwedge hlt
  exact
    freeQ2DoubledFullOriginConnProb_le_of_expectationJ_le
      (hJ hvwedge hlt)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal := by
  intro β hβpos n v hvwedge hlt hypos
  exact
    freeQ2DoubledFullOriginConnProb_le_of_expectationJ_le
      (hJ hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_expectationJAt
    {β : ℝ} {hβpos : 0 < β} {n : ℕ}
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt
      β hβpos n := by
  intro v hvwedge hlt hypos
  exact
    freeQ2DoubledFullOriginConnProb_le_of_expectationJ_le
      (hJ v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_expectationJPositiveSubcritical
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical := by
  intro β hβpos hβc
  exact Filter.Eventually.mono (hJ β hβpos hβc) fun n hn =>
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonAt_of_expectationJAt
      (hβpos := hβpos) hn


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal_of_expectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal := by
  intro β hβpos n v hvwedge hheight hnotlt
  exact
    freeQ2DoubledFullOriginConnProb_le_of_expectationJ_le
      (hJ hvwedge hheight hnotlt)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_expectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal_of_expectationJ
      hJ)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_expectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hJ)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_expectationJ
    (hJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal_of_expectationJ
      hJ)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCasesExpectationJY
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hstrictYJ)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJY
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCasesExpectationJY
      hstrictZ hdiagY hstrictYJ)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCases
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonPositiveSubcritical_of_local
      hstrictZ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonPositiveSubcritical_of_local
      hdiagY)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonPositiveSubcritical_of_expectationJPositiveSubcritical
      hstrictYJ)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcert :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical
      hcert)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbudget :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentExpectationJSplitPositiveSubcritical_of_finiteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
      hbudget hJsplit)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical
      htable)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical
      htable)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical
      htable)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical
      htable)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical
      htable)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityTotalSelectedCopySixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityTotalSelectedCopySixthFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityTotalSelectedCopySixthFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_emptyBoundPositiveSubcritical_innerPairBoundPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_activeResidualBranchSixthFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchOwnerPairShareSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchOwnerPairShareSixthFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_ownerPairShareSixthFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical
      hbounds)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hroutes :
      ExactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_exactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical
      hroutes)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hprofile :
      ExactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (exactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical_of_profileWitnessRouteShareBoundsPositiveSubcritical
      hprofile)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hsource :
      ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (exactSupportOwnerResidualSourcePairRouteShareBoundsPositiveSubcritical_of_sourceEquationRouteShareBoundsPositiveSubcritical
      hsource)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsPositiveSubcritical)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_of_empty_innerSourceEquationRouteShareBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationCellRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsPositiveSubcritical)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsPositiveSubcritical_of_empty_innerSourceEquationCellRouteShareBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsPositiveSubcritical)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellRouteShareBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsPositiveSubcritical)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellRouteShareBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
      hcover)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical
      hcover)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcover :
      ExactSupportOwnerResidualSourcePairEmptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (exactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsPositiveSubcritical_of_emptyInnerSplitSourceEquationFiniteCellCoverRouteShareBoundsPositiveSubcritical
      hcover)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_activeResidualBranchEmptyInnerSixthFiniteSumBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_residualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_activeResidualBranchSixthFiniteSumMajorantBoundsPositiveSubcritical
      hmajorant)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsPositiveSubcritical_of_activeResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumMajorantBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundPositiveSubcritical_of_residualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundPositiveSubcritical_of_residualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical
        hinner)
      hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical_of_activeResidualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical_of_activeResidualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical
      hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumSourcePairInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical_of_residualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical_of_residualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundPositiveSubcritical
      hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundPositiveSubcritical_of_residualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical
      hempty)
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundPositiveSubcritical_of_residualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical
        hinner)
      hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical
      hempty)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical
      hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchUpdateSelectedEdgeMultiplicityFilterRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonUpdateSelectedEdgeMultiplicityFilterRouteBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
  let hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical :=
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_of_updateSelectedEdgeMultiplicityFilterRouteBoundsPositiveSubcritical
      hroute
  have hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical := by
    intro β hβpos hβc
    exact Filter.Eventually.mono (hdata β hβpos hβc) fun _ hn => hn.1
  have hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical := by
    intro β hβpos hβc
    exact Filter.Eventually.mono (hdata β hβpos hβc) fun _ hn => hn.2
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchMultiplicityFilterRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchUpdateSelectedEdgeMultiplicityFilterRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonUpdateSelectedEdgeMultiplicityFilterRouteBoundsPositiveSubcritical_of_multiplicityFilterRouteBoundsPositiveSubcritical
      hroute)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchMultiplicityFilterPointwiseSourceEquationRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchMultiplicityFilterRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsPositiveSubcritical_of_pointwiseSourceEquationRouteBoundsPositiveSubcritical
      hroute)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerMultiplicityFilterPointwiseSourceEquationRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchMultiplicityFilterPointwiseSourceEquationRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundsPositiveSubcritical_of_empty_inner_pointwiseSourceEquationRouteBoundPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchOwnerSupportSingletonPointwiseSourceEquationRouteBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical := by
  let hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical :=
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_of_ownerSupportSingletonPointwiseSourceEquationRouteBoundsPositiveSubcritical
      hroute
  have hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical := by
    intro β hβpos hβc
    exact Filter.Eventually.mono (hdata β hβpos hβc) fun _ hn => hn.1
  have hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundPositiveSubcritical := by
    intro β hβpos hβc
    exact Filter.Eventually.mono (hdata β hβpos hβc) fun _ hn => hn.2
  exact
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsPositiveSubcritical_expectationJSplitPositiveSubcritical
      hstrictZ hdiagY hempty hinner hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsPositiveSubcritical_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hcontract :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentFiniteBudgetPositiveSubcritical_of_filterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsPositiveSubcritical
      hcontract)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBoundsExpectationJSplitPositiveSubcritical
      hstrictYBounds)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hstrictYBounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBoundsExpectationJRatioGapPositiveSubcritical
      hstrictYBounds)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJSplitPositiveSubcritical
      hbounds hJsplit)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJRatioGapPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical)
    (hratio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJYPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJRatioGapPositiveSubcritical
      hbounds hratio)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentEmptyInnerBounds_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyBoundPositiveSubcritical_innerPairBoundPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentEmptyInnerBounds_expectationJRatioGapPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairBoundPositiveSubcritical)
    (hratio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJRatioGapPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_emptyBoundPositiveSubcritical_innerPairBoundPositiveSubcritical
      hempty hinner)
    hratio

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentSelectedCopyBounds_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_selectedCopyBoundsPositiveSubcritical
      hselected)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentSelectedCopyBounds_expectationJRatioGapPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hselected :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical)
    (hratio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentBounds_expectationJRatioGapPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsPositiveSubcritical_of_selectedCopyBoundsPositiveSubcritical
      hselected)
    hratio

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBounds_expectationJSplitPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical)
    (hJsplit :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJSplitPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentSelectedCopyBounds_expectationJSplitPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical_of_selectedCopyEmptyBoundPositiveSubcritical_selectedCopyInnerPairBoundPositiveSubcritical
      hempty hinner)
    hJsplit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentSelectedCopyEmptyInnerBounds_expectationJRatioGapPositiveSubcritical
    (hstrictZ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal)
    (hdiagY :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal)
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyBoundPositiveSubcritical)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairBoundPositiveSubcritical)
    (hratio :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYExpectationJRatioGapPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_sourceSectorResidualMomentBranchComponentSelectedCopyBounds_expectationJRatioGapPositiveSubcritical
    hstrictZ hdiagY
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyBoundsPositiveSubcritical_of_selectedCopyEmptyBoundPositiveSubcritical_selectedCopyInnerPairBoundPositiveSubcritical
      hempty hinner)
    hratio


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCasesExpectationJ
    (hstrictZJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
    (hdiagYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCases
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorComparisonLocal_of_expectationJ
      hstrictZJ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorComparisonLocal_of_expectationJ
      hdiagYJ)
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorComparisonLocal_of_expectationJ
      hstrictYJ)


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_predecessorCasesExpectationJ
    (hstrictZJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorPredecessorExpectationJComparisonLocal)
    (hdiagYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullDiagonalPredecessorExpectationJComparisonLocal)
    (hstrictYJ :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonLocal) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentPositiveSubcritical_of_local
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullOneEdgeDescentLocal_of_predecessorCasesExpectationJ
      hstrictZJ hdiagYJ hstrictYJ)

end Exact3D
end StatMech
