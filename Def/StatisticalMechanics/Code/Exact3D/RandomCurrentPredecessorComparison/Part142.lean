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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part149
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBranchwiseOriginIncidentEdgeOwnerRelaxedExplicitCaseTableBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                ∃ κEmpty : Type,
                  ∃ κInner : Type,
                    ∃ emptyCaseSet :
                      ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                        Finset κEmpty,
                      ∃ emptyCaseOf :
                        ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) →
                            κEmpty,
                        ∃ emptyRowBound :
                          ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                            κEmpty → ℝ,
                          ∃ emptyRelaxedBudget :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                              κEmpty → ℝ,
                            ∃ innerCaseSet :
                              ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                Finset κInner,
                              ∃ innerCaseOf :
                                ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                  (↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                      ℕ) →
                                    κInner,
                                ∃ innerRowBound :
                                  ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                    κInner → ℝ,
                                  ∃ innerRelaxedBudget :
                                    ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                      κInner → ℝ,
                                    (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                      ∀ m ∈
                                          Ω.filter
                                            (fun m =>
                                              doubledBoxOriginIncidentOwner
                                                  n m =
                                                some ew),
                                        emptyCaseOf ew m ∈
                                          emptyCaseSet ew) ∧
                                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                        ∀ m ∈
                                            Ω.filter
                                              (fun m =>
                                                doubledBoxOriginIncidentOwner
                                                    n m =
                                                  some ew),
                                          innerCaseOf ew m ∈
                                            innerCaseSet ew) ∧
                                        (∀ ew ∈
                                            doubledBoxOriginIncidentEdges n,
                                          ∀ m ∈
                                              Ω.filter
                                                (fun m =>
                                                  doubledBoxOriginIncidentOwner
                                                      n m =
                                                    some ew),
                                            doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                              β n v
                                              (boxVertStrictSectorYPredecessor3
                                                v hvwedge hlt hypos)
                                              e0 m ≤
                                              emptyRowBound ew
                                                (emptyCaseOf ew m)) ∧
                                          (∀ ew ∈
                                              doubledBoxOriginIncidentEdges n,
                                            ∀ m ∈
                                                Ω.filter
                                                  (fun m =>
                                                    doubledBoxOriginIncidentOwner
                                                        n m =
                                                      some ew),
                                              doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                                β n v
                                                (boxVertStrictSectorYPredecessor3
                                                  v hvwedge hlt hypos)
                                                e0 m ≤
                                                innerRowBound ew
                                                  (innerCaseOf ew m)) ∧
                                            (∀ ew ∈
                                                doubledBoxOriginIncidentEdges n,
                                              ∀ c ∈ emptyCaseSet ew,
                                                emptyRowBound ew c ≤
                                                  emptyRelaxedBudget ew c) ∧
                                              (∀ ew ∈
                                                  doubledBoxOriginIncidentEdges
                                                    n,
                                                ∀ c ∈ innerCaseSet ew,
                                                  innerRowBound ew c ≤
                                                    innerRelaxedBudget ew c) ∧
                                                (∑ ew ∈
                                                    doubledBoxOriginIncidentEdges
                                                      n,
                                                  finiteSupportExplicitCaseBudgetTotal
                                                    (Ω.filter
                                                      (fun m =>
                                                        doubledBoxOriginIncidentOwner
                                                            n m =
                                                          some ew))
                                                    (emptyCaseOf ew)
                                                    (emptyCaseSet ew)
                                                    (emptyRelaxedBudget ew)) ≤
                                                  doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                                    β n v ∧
                                                  (∑ ew ∈
                                                      doubledBoxOriginIncidentEdges
                                                        n,
                                                    finiteSupportExplicitCaseBudgetTotal
                                                      (Ω.filter
                                                        (fun m =>
                                                          doubledBoxOriginIncidentOwner
                                                              n m =
                                                            some ew))
                                                      (innerCaseOf ew)
                                                      (innerCaseSet ew)
                                                      (innerRelaxedBudget ew)) ≤
                                                    Sharpness.sourcePairSum
                                                      (FK.boxGraph 3 (2 * n))
                                                      β (fun _ => 1)
                                                      (doubledBoxOriginToInnerEndpointSource
                                                        n
                                                        (boxVertStrictSectorYPredecessor3
                                                          v hvwedge hlt
                                                          hypos))
                                                      (doubledBoxInnerPairSource
                                                        n v
                                                        (boxVertStrictSectorYPredecessor3
                                                          v hvwedge hlt
                                                          hypos))

end Exact3D
end StatMech
