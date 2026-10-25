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
import Structure.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part14
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_rows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgeStrictSectorYPredecessorExpectationJRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  let p :
      {u : FK.boxVerts 3 n //
        boxVertPositiveXFaceOrderedWedge3 n u ∧
          ((u : Lattice.Site 3) (1 : Fin 3)) <
            ((u : Lattice.Site 3) (2 : Fin 3)) ∧
              0 < ((u : Lattice.Site 3) (1 : Fin 3))} :=
    ⟨v, hvwedge, hlt, hypos⟩
  exact T.sound p (hrows (T.classify p) (T.covers p))


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_currentSumRows
    {β : ℝ} {n : ℕ} {Case : Type*} [DecidableEq Case]
    (T : OrderedWedgeStrictSectorYPredecessorCurrentSumRowsAt β n Case)
    (hrows : ∀ c, c ∈ T.rows → T.rowPred c) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_currentSum_le
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorCurrentSumComparisonAt_of_rows
        T hrows v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_absorption
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hfinite :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    (∑ m' ∈ Ω.image
                        (fun m => Function.update m e0 (m e0 + 1)),
                      ((m' e0 : ℕ) : ℝ) *
                        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β
                          n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                            hypos) m') ≤
                      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n
                        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                          hypos))
    (habsorb :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n v
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) ≤
                β *
                  doubledBoxOriginToInnerEndpointSourcePairEmptySum β n
                    (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitAbsorption
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_selectedCopySplitBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos.le hvwedge hlt hypos
        (hfinite v hvwedge hlt hypos))
      (habsorb v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_sourcePairSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hfinite :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    (∑ m' ∈ Ω.image
                        (fun m => Function.update m e0 (m e0 + 1)),
                      ((m' e0 : ℕ) : ℝ) *
                        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β
                          n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                            hypos) m') ≤
                      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n
                        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                          hypos))
    (hsplit :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                    (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                    (doubledBoxInnerPairSource n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) ≤
                doubledBoxOriginToInnerEndpointSourcePairEmptySum β n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_absorption
    hβpos hfinite
    (fun v hvwedge hlt hypos =>
      doubledBoxOriginToInnerEndpointSelectedCopySplitBound_le_beta_mul_sourcePairEmptySum_of_sourcePairSplit_le
        hβpos.le n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
        (by
          simpa [doubledBoxOriginToInnerEndpointSourcePairSplitScalar] using
            hsplit v hvwedge hlt hypos))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_expectationJSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hfinite :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    (∑ m' ∈ Ω.image
                        (fun m => Function.update m e0 (m e0 + 1)),
                      ((m' e0 : ℕ) : ℝ) *
                        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β
                          n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                            hypos) m') ≤
                      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n
                        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                          hypos))
    (hJsplit :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v) +
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w) *
                  Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxInnerPairSource n v w) ≤
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJSplit
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_selectedCopySplitBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos.le hvwedge hlt hypos
        (hfinite v hvwedge hlt hypos))
      (by
        simpa using hJsplit v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointExpectationJ_pos_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    0 < Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
      (doubledBoxOriginToInnerEndpointSource n
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
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
        hvwedge hwwedge hheight hadj with
    ⟨_e0, _hedge, _hov, how, _hvw⟩
  simpa [w] using
    doubledBoxOriginToInnerEndpointExpectationJ_pos_of_endpoint_ne
      (β := β) hβpos (n := n) (v := w) how

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointSourcePairEmptySum_pos_of_strictSectorYPredecessorRow3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    0 < doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
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
        hvwedge hwwedge hheight hadj with
    ⟨_e0, _hedge, hov, _how, _hvw⟩
  exact
    doubledBoxOriginToInnerEndpointSourcePairEmptySum_pos_of_endpoint_ne
      (β := β) hβpos (n := n) (v := v) hov

set_option linter.style.longLine false in


theorem doubledBoxOriginToInnerEndpointInnerPairSourcePairSum_pos_of_strictSectorYPredecessor3
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) :
    0 <
      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
        (doubledBoxInnerPairSource n v
          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  have hwwedge : boxVertPositiveXFaceOrderedWedge3 n w := by
    simpa [w] using
      boxVertStrictSectorYPredecessor3_wedge v hvwedge hlt hypos
  have hheight : boxVertTransverseHeight3 w < boxVertTransverseHeight3 v := by
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
        hvwedge hwwedge hheight hadj with
    ⟨_e0, _hedge, _hov, how, hvw⟩
  simpa [w] using
    doubledBoxOriginToInnerEndpointInnerPairSourcePairSum_pos_of_endpoints_ne
      (β := β) hβpos (n := n) (v := v) (w := w) how hvw

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_expectationJRatioGap
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hfinite :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    (∑ m' ∈ Ω.image
                        (fun m => Function.update m e0 (m e0 + 1)),
                      ((m' e0 : ℕ) : ℝ) *
                        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β
                          n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                            hypos) m') ≤
                      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n
                        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                          hypos))
    (hpos :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              0 < Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n w))
    (hratio :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v) /
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w) +
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxInnerPairSource n v w) ≤ 1) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJRatioGap
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_selectedCopySplitBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos.le hvwedge hlt hypos
        (hfinite v hvwedge hlt hypos))
      (by
        simpa using hpos v hvwedge hlt hypos)
      (by
        simpa using hratio v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_expectationJRatioGap_autoPos
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hfinite :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    (∑ m' ∈ Ω.image
                        (fun m => Function.update m e0 (m e0 + 1)),
                      ((m' e0 : ℕ) : ℝ) *
                        doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm β
                          n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                            hypos) m') ≤
                      doubledBoxOriginToInnerEndpointSelectedCopySplitBound β n
                        v (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                          hypos))
    (hratio :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v) /
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w) +
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxInnerPairSource n v w) ≤ 1) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_selectedCopySplitFiniteImageBound_expectationJRatioGap
    hβpos hfinite
    (fun v hvwedge hlt hypos =>
      doubledBoxOriginToInnerEndpointExpectationJ_pos_of_strictSectorYPredecessor3
        hβpos v hvwedge hlt hypos)
    hratio

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_totalPairCardSourcePairSummandTsumBound_expectationJRatioGap_autoPos
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hsum :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
                    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m))
    (hbound :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m) ≤
                    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                        (doubledBoxInnerPairSource n v
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hratio :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v) /
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w) +
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxInnerPairSource n v w) ≤ 1) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJRatioGap
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandTsumBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos.le hvwedge hlt hypos
        (hsum v hvwedge hlt hypos)
        (hbound v hvwedge hlt hypos))
      (doubledBoxOriginToInnerEndpointExpectationJ_pos_of_strictSectorYPredecessor3
        hβpos v hvwedge hlt hypos)
      (by
        simpa using hratio v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_totalPairCardSourcePairSummandTsumBound_expectationJSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hsum :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
                    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m))
    (hbound :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    doubledBoxSelectedCopyTotalPairCardSourcePairSummand β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m) ≤
                    doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v +
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                        (doubledBoxInnerPairSource n v
                          (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)))
    (hJsplit :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v) +
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w) *
                  Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxInnerPairSource n v w) ≤
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJSplit
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_totalPairCardSourcePairSummandTsumBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos.le hvwedge hlt hypos
        (hsum v hvwedge hlt hypos)
        (hbound v hvwedge hlt hypos))
      (by
        simpa using hJsplit v hvwedge hlt hypos)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt_of_sourceSectorResidualMomentBranchSummandTsumBound_expectationJSplit
    {β : ℝ} (hβpos : 0 < β) {n : ℕ}
    (hsum :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  Summable (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
                    doubledBoxSourceSectorResidualMomentBranchSummand β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m))
    (hbound :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n)
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) →
                  (∑' m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                    doubledBoxSourceSectorResidualMomentBranchSummand β n v
                      (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)
                      e0 m) ≤
                    β *
                      (doubledBoxOriginToInnerEndpointSourcePairEmptySum β n
                        v +
                        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                          (fun _ => 1)
                          (doubledBoxOriginToInnerEndpointSource n
                            (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                              hypos))
                          (doubledBoxInnerPairSource n v
                            (boxVertStrictSectorYPredecessor3 v hvwedge hlt
                              hypos))))
    (hJsplit :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n v) +
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n w) *
                  Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (doubledBoxInnerPairSource n v w) ≤
                Sharpness.expectationJ (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                  (doubledBoxOriginToInnerEndpointSource n w)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYPredecessorExpectationJComparisonAt
      β n := by
  intro v hvwedge hlt hypos
  exact
    doubledBoxOriginToInnerEndpointExpectationJ_le_of_selectedCopySplitExpectationJSplit
      hβpos
      (beta_mul_doubledBoxOriginToInnerEndpointEdgeCopyCollapsedSum_le_sourceSectorResidualMomentBranchSummandTsumBound_of_strictSectorYPredecessor3
        (β := β) (n := n) (v := v) hβpos hvwedge hlt hypos
        (hsum v hvwedge hlt hypos)
        (hbound v hvwedge hlt hypos))
      (by
        simpa using hJsplit v hvwedge hlt hypos)

end Exact3D
end StatMech
