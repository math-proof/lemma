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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part94
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerRelaxedExplicitCaseTableFiniteBudgetAt
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
                      ∃ rowBound :
                        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                        ∃ relaxedBudget :
                          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                          (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈
                              (Ω.filter
                                (doubledBoxIncrementedFullSourceActive n w
                                  e0)).filter
                                (fun m =>
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
                              caseOf ew m ∈ caseSet ew) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈
                                (Ω.filter
                                  (doubledBoxIncrementedFullSourceActive n w
                                    e0)).filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                                (((edgeCopySourceSector
                                  (FK.boxGraph 3 (2 * n))
                                  (doubledBoxOriginToInnerEndpointSource n v)
                                  (Function.update m e0
                                    (m e0 + 1))).card : ℕ) : ℝ) *
                                  doubledBoxResidualMomentBranchSummand β n v
                                    w e0 m ≤
                                  rowBound ew (caseOf ew m)) ∧
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ c ∈ caseSet ew,
                                  rowBound ew c ≤ relaxedBudget ew c) ∧
                                (∑ ew ∈ doubledBoxOriginIncidentEdges n,
                                  finiteSupportExplicitCaseBudgetTotal
                                    ((Ω.filter
                                      (doubledBoxIncrementedFullSourceActive n
                                        w e0)).filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew))
                                    (caseOf ew) (caseSet ew)
                                    (relaxedBudget ew)) ≤
                                  β *
                                    (doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                        β n v +
                                      Sharpness.sourcePairSum
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource
                                          n w)
                                        (doubledBoxInnerPairSource n v w))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerSixthRelaxedExplicitCaseTableFiniteBudgetAt
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
                      ∃ rowBound :
                        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                        ∃ relaxedBudget :
                          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                          (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈
                              (Ω.filter
                                (doubledBoxIncrementedFullSourceActive n w
                                  e0)).filter
                                (fun m =>
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
                              caseOf ew m ∈ caseSet ew) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈
                                (Ω.filter
                                  (doubledBoxIncrementedFullSourceActive n w
                                    e0)).filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                                (((edgeCopySourceSector
                                  (FK.boxGraph 3 (2 * n))
                                  (doubledBoxOriginToInnerEndpointSource n v)
                                  (Function.update m e0
                                    (m e0 + 1))).card : ℕ) : ℝ) *
                                  doubledBoxResidualMomentBranchSummand β n v
                                    w e0 m ≤
                                  rowBound ew (caseOf ew m)) ∧
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ c ∈ caseSet ew,
                                  rowBound ew c ≤ relaxedBudget ew c) ∧
                                (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  finiteSupportExplicitCaseBudgetTotal
                                    ((Ω.filter
                                      (doubledBoxIncrementedFullSourceActive n
                                        w e0)).filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew))
                                    (caseOf ew) (caseSet ew)
                                    (relaxedBudget ew) ≤
                                  (β *
                                    (doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                        β n v +
                                      Sharpness.sourcePairSum
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource
                                          n w)
                                        (doubledBoxInnerPairSource n v w))) /
                                    6)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseSixthRelaxedExplicitCaseTableFiniteBudgetAt
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
                      ∃ rowBoundEmpty :
                        ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                        ∃ rowBoundInner :
                          ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                          ∃ relaxedBudgetEmpty :
                            ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                            ∃ relaxedBudgetInner :
                              ↥(FK.boxGraph 3 (2 * n)).edgeFinset → κ → ℝ,
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                  (Ω.filter
                                    (doubledBoxIncrementedFullSourceActive n w
                                      e0)).filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                  caseOf ew m ∈ caseSet ew) ∧
                                (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈
                                    (Ω.filter
                                      (doubledBoxIncrementedFullSourceActive n
                                        w e0)).filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                      β n v w e0 m ≤
                                      rowBoundEmpty ew (caseOf ew m)) ∧
                                  (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                    ∀ m ∈
                                      (Ω.filter
                                        (doubledBoxIncrementedFullSourceActive
                                          n w e0)).filter
                                        (fun m =>
                                          doubledBoxOriginIncidentOwner n m =
                                            some ew),
                                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                        β n v w e0 m ≤
                                        rowBoundInner ew (caseOf ew m)) ∧
                                    (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                      ∀ c ∈ caseSet ew,
                                        rowBoundEmpty ew c ≤
                                          relaxedBudgetEmpty ew c) ∧
                                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                        ∀ c ∈ caseSet ew,
                                          rowBoundInner ew c ≤
                                            relaxedBudgetInner ew c) ∧
                                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                          finiteSupportExplicitCaseBudgetTotal
                                            ((Ω.filter
                                              (doubledBoxIncrementedFullSourceActive
                                                n w e0)).filter
                                              (fun m =>
                                                doubledBoxOriginIncidentOwner n
                                                  m = some ew))
                                            (caseOf ew) (caseSet ew)
                                            (relaxedBudgetEmpty ew) ≤
                                          (β *
                                            doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                              β n v) / 6) ∧
                                          (∀ ew ∈
                                            doubledBoxOriginIncidentEdges n,
                                            finiteSupportExplicitCaseBudgetTotal
                                              ((Ω.filter
                                                (doubledBoxIncrementedFullSourceActive
                                                  n w e0)).filter
                                                (fun m =>
                                                  doubledBoxOriginIncidentOwner
                                                    n m = some ew))
                                              (caseOf ew) (caseSet ew)
                                              (relaxedBudgetInner ew) ≤
                                            (β *
                                              Sharpness.sourcePairSum
                                                (FK.boxGraph 3 (2 * n)) β
                                                (fun _ => 1)
                                                (doubledBoxOriginToInnerEndpointSource
                                                  n w)
                                                (doubledBoxInnerPairSource
                                                  n v w)) / 6)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentOriginIncidentEdgeOwnerBranchwiseFourBetaSixthContractionsAt
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
              (2 * β) *
                  Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n))
                    (2 * (2 * β)) (fun _ => 1)
                    (doubledBoxOriginToInnerEndpointSource n v)
                    (∅ : Finset (FK.boxVerts 3 (2 * n))) ≤
                (β *
                  doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
                  6 ∧
                (2 * β) *
                    Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n))
                      (2 * (2 * β)) (fun _ => 1)
                      (doubledBoxOriginToInnerEndpointSource n w)
                      (doubledBoxInnerPairSource n v w) ≤
                  (β *
                    Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                      (fun _ => 1)
                      (doubledBoxOriginToInnerEndpointSource n w)
                      (doubledBoxInnerPairSource n v w)) /
                    6

end Exact3D
end StatMech
