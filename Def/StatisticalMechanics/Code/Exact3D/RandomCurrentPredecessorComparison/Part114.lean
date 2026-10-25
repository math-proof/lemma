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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part121
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseInOutSelectedCopySixthRelaxedExplicitCaseTableFiniteBudgetAt
    (β : ℝ) (n : ℕ) : Prop :=
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
          let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
          ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
            e0.1 =
                s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                  FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
              ∀ Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                ∃ κ : Type,
                  ∃ caseSet :
                    ↥(FK.boxGraph 3 (2 * n)).edgeFinset → Finset κ,
                    ∃ caseOf :
                      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ,
                      ∃ rowBoundEmptyIn :
                        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                        ∃ rowBoundEmptyOutside :
                          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                          ∃ rowBoundInnerIn :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                            ∃ rowBoundInnerOutside :
                              ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                κ → ℝ,
                              ∃ relaxedBudgetEmptyIn :
                                ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                  κ → ℝ,
                                ∃ relaxedBudgetEmptyOutside :
                                  ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                    κ → ℝ,
                                  ∃ relaxedBudgetInnerIn :
                                    ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                      κ → ℝ,
                                    ∃ relaxedBudgetInnerOutside :
                                      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                        κ → ℝ,
                                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                        ∀ m ∈
                                          (Ω.filter
                                            (doubledBoxIncrementedFullSourceActive
                                              n w e0)).filter
                                            (fun m =>
                                              doubledBoxOriginIncidentOwner n
                                                m = some ew),
                                          caseOf ew m ∈ caseSet ew) ∧
                                        (∀ ew ∈
                                            doubledBoxOriginIncidentEdges n,
                                          ∀ m ∈
                                            (Ω.filter
                                              (doubledBoxIncrementedFullSourceActive
                                                n w e0)).filter
                                              (fun m =>
                                                doubledBoxOriginIncidentOwner n
                                                  m = some ew),
                                            β *
                                              doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                                                β n v w e0 m ≤
                                              rowBoundEmptyIn ew
                                                (caseOf ew m)) ∧
                                          (∀ ew ∈
                                              doubledBoxOriginIncidentEdges n,
                                            ∀ m ∈
                                              (Ω.filter
                                                (doubledBoxIncrementedFullSourceActive
                                                  n w e0)).filter
                                                (fun m =>
                                                  doubledBoxOriginIncidentOwner
                                                    n m = some ew),
                                              β *
                                                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                                                  β n v w e0 m ≤
                                                rowBoundEmptyOutside ew
                                                  (caseOf ew m)) ∧
                                            (∀ ew ∈
                                                doubledBoxOriginIncidentEdges n,
                                              ∀ m ∈
                                                (Ω.filter
                                                  (doubledBoxIncrementedFullSourceActive
                                                    n w e0)).filter
                                                  (fun m =>
                                                    doubledBoxOriginIncidentOwner
                                                      n m = some ew),
                                                β *
                                                  doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                                                    β n v w e0 m ≤
                                                  rowBoundInnerIn ew
                                                    (caseOf ew m)) ∧
                                              (∀ ew ∈
                                                  doubledBoxOriginIncidentEdges
                                                    n,
                                                ∀ m ∈
                                                  (Ω.filter
                                                    (doubledBoxIncrementedFullSourceActive
                                                      n w e0)).filter
                                                    (fun m =>
                                                      doubledBoxOriginIncidentOwner
                                                        n m = some ew),
                                                  β *
                                                    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                                                      β n v w e0 m ≤
                                                    rowBoundInnerOutside ew
                                                      (caseOf ew m)) ∧
                                                (∀ ew ∈
                                                    doubledBoxOriginIncidentEdges
                                                      n,
                                                  ∀ c ∈ caseSet ew,
                                                    rowBoundEmptyIn ew c ≤
                                                      relaxedBudgetEmptyIn ew
                                                        c) ∧
                                                  (∀ ew ∈
                                                      doubledBoxOriginIncidentEdges
                                                        n,
                                                    ∀ c ∈ caseSet ew,
                                                      rowBoundEmptyOutside ew
                                                          c ≤
                                                        relaxedBudgetEmptyOutside
                                                          ew c) ∧
                                                    (∀ ew ∈
                                                        doubledBoxOriginIncidentEdges
                                                          n,
                                                      ∀ c ∈ caseSet ew,
                                                        rowBoundInnerIn ew c ≤
                                                          relaxedBudgetInnerIn
                                                            ew c) ∧
                                                      (∀ ew ∈
                                                          doubledBoxOriginIncidentEdges
                                                            n,
                                                        ∀ c ∈ caseSet ew,
                                                          rowBoundInnerOutside
                                                              ew c ≤
                                                            relaxedBudgetInnerOutside
                                                              ew c) ∧
                                                        (∀ ew ∈
                                                            doubledBoxOriginIncidentEdges
                                                              n,
                                                          finiteSupportExplicitCaseBudgetTotal
                                                            ((Ω.filter
                                                              (doubledBoxIncrementedFullSourceActive
                                                                n w e0)).filter
                                                              (fun m =>
                                                                doubledBoxOriginIncidentOwner
                                                                  n m =
                                                                  some ew))
                                                            (caseOf ew)
                                                            (caseSet ew)
                                                            (fun c =>
                                                              relaxedBudgetEmptyIn
                                                                  ew c +
                                                                relaxedBudgetEmptyOutside
                                                                  ew c) ≤
                                                            (β *
                                                              doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                                                β n v) / 6) ∧
                                                          (∀ ew ∈
                                                            doubledBoxOriginIncidentEdges
                                                              n,
                                                            finiteSupportExplicitCaseBudgetTotal
                                                              ((Ω.filter
                                                                (doubledBoxIncrementedFullSourceActive
                                                                  n w e0)).filter
                                                                (fun m =>
                                                                  doubledBoxOriginIncidentOwner
                                                                    n m =
                                                                    some ew))
                                                              (caseOf ew)
                                                              (caseSet ew)
                                                              (fun c =>
                                                                relaxedBudgetInnerIn
                                                                    ew c +
                                                                  relaxedBudgetInnerOutside
                                                                    ew c) ≤
                                                              (β *
                                                                Sharpness.sourcePairSum
                                                                  (FK.boxGraph 3
                                                                    (2 * n))
                                                                  β (fun _ => 1)
                                                                  (doubledBoxOriginToInnerEndpointSource
                                                                    n w)
                                                                  (doubledBoxInnerPairSource
                                                                    n v w)) /
                                                                6)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
    (β : ℝ) (n : ℕ) : Prop :=
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  ∀ v : FK.boxVerts 3 n,
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
      (hlt :
        ((v : Lattice.Site 3) (1 : Fin 3)) <
          ((v : Lattice.Site 3) (2 : Fin 3))) →
        (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
          let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
          ∀ e0 : Edge,
            e0.1 =
                s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                  FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
              ∀ Ω : Finset Profile,
                let Ωupdate : Edge → Finset Profile :=
                  fun ew =>
                    (Ω.filter
                      (doubledBoxIncrementedFullSourceActive n w e0)).filter
                      (fun m =>
                        (Function.update m e0 (m e0 + 1)) ew ≠ 0)
                ∃ κ : Type,
                  ∃ caseSet : Edge → Finset κ,
                    ∃ caseOf : Edge → Profile → κ,
                      ∃ rowBoundEmptyIn : Edge → κ → ℝ,
                        ∃ rowBoundEmptyOutside : Edge → κ → ℝ,
                          ∃ rowBoundInnerIn : Edge → κ → ℝ,
                            ∃ rowBoundInnerOutside : Edge → κ → ℝ,
                              ∃ relaxedBudgetEmptyIn : Edge → κ → ℝ,
                                ∃ relaxedBudgetEmptyOutside : Edge → κ → ℝ,
                                  ∃ relaxedBudgetInnerIn : Edge → κ → ℝ,
                                    ∃ relaxedBudgetInnerOutside :
                                      Edge → κ → ℝ,
                                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                        ∀ m ∈ Ωupdate ew,
                                          caseOf ew m ∈ caseSet ew) ∧
                                        (∀ ew ∈
                                            doubledBoxOriginIncidentEdges n,
                                          ∀ m ∈ Ωupdate ew,
                                            β *
                                              doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                                                β n v w e0 m ≤
                                              rowBoundEmptyIn ew
                                                (caseOf ew m)) ∧
                                          (∀ ew ∈
                                              doubledBoxOriginIncidentEdges n,
                                            ∀ m ∈ Ωupdate ew,
                                              β *
                                                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                                                  β n v w e0 m ≤
                                                rowBoundEmptyOutside ew
                                                  (caseOf ew m)) ∧
                                            (∀ ew ∈
                                                doubledBoxOriginIncidentEdges n,
                                              ∀ m ∈ Ωupdate ew,
                                                β *
                                                  doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                                                    β n v w e0 m ≤
                                                  rowBoundInnerIn ew
                                                    (caseOf ew m)) ∧
                                              (∀ ew ∈
                                                  doubledBoxOriginIncidentEdges
                                                    n,
                                                ∀ m ∈ Ωupdate ew,
                                                  β *
                                                    doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                                                      β n v w e0 m ≤
                                                    rowBoundInnerOutside ew
                                                      (caseOf ew m)) ∧
                                                (∀ ew ∈
                                                    doubledBoxOriginIncidentEdges
                                                      n,
                                                  ∀ c ∈ caseSet ew,
                                                    rowBoundEmptyIn ew c ≤
                                                      relaxedBudgetEmptyIn ew
                                                        c) ∧
                                                  (∀ ew ∈
                                                      doubledBoxOriginIncidentEdges
                                                        n,
                                                    ∀ c ∈ caseSet ew,
                                                      rowBoundEmptyOutside ew
                                                          c ≤
                                                        relaxedBudgetEmptyOutside
                                                          ew c) ∧
                                                    (∀ ew ∈
                                                        doubledBoxOriginIncidentEdges
                                                          n,
                                                      ∀ c ∈ caseSet ew,
                                                        rowBoundInnerIn ew c ≤
                                                          relaxedBudgetInnerIn
                                                            ew c) ∧
                                                      (∀ ew ∈
                                                          doubledBoxOriginIncidentEdges
                                                            n,
                                                        ∀ c ∈ caseSet ew,
                                                          rowBoundInnerOutside
                                                              ew c ≤
                                                            relaxedBudgetInnerOutside
                                                              ew c) ∧
                                                        (∀ ew ∈
                                                            doubledBoxOriginIncidentEdges
                                                              n,
                                                          ∀ c ∈ caseSet ew,
                                                            0 ≤
                                                              relaxedBudgetEmptyIn
                                                                  ew c +
                                                                relaxedBudgetEmptyOutside
                                                                  ew c) ∧
                                                          (∀ ew ∈
                                                              doubledBoxOriginIncidentEdges
                                                                n,
                                                            ∀ c ∈ caseSet ew,
                                                              0 ≤
                                                                relaxedBudgetInnerIn
                                                                    ew c +
                                                                  relaxedBudgetInnerOutside
                                                                    ew c) ∧
                                                            (∀ ew ∈
                                                                doubledBoxOriginIncidentEdges
                                                                  n,
                                                              finiteSupportExplicitCaseBudgetTotal
                                                                (Ωupdate ew)
                                                                (caseOf ew)
                                                                (caseSet ew)
                                                                (fun c =>
                                                                  relaxedBudgetEmptyIn
                                                                      ew c +
                                                                    relaxedBudgetEmptyOutside
                                                                      ew c) ≤
                                                                (β *
                                                                  doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                                                    β n v) / 6) ∧
                                                              (∀ ew ∈
                                                                doubledBoxOriginIncidentEdges
                                                                  n,
                                                                finiteSupportExplicitCaseBudgetTotal
                                                                  (Ωupdate ew)
                                                                  (caseOf ew)
                                                                  (caseSet ew)
                                                                  (fun c =>
                                                                    relaxedBudgetInnerIn
                                                                        ew c +
                                                                      relaxedBudgetInnerOutside
                                                                        ew c) ≤
                                                                  (β *
                                                                    Sharpness.sourcePairSum
                                                                      (FK.boxGraph 3
                                                                        (2 * n))
                                                                      β (fun _ => 1)
                                                                      (doubledBoxOriginToInnerEndpointSource
                                                                        n w)
                                                              (doubledBoxInnerPairSource
                                                                n v w)) /
                                                                    6)

end Exact3D
end StatMech
