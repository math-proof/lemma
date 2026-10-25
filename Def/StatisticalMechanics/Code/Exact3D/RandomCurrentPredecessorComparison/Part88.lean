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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part95
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
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
                                        ∀ m ∈ Ωtouch,
                                          caseOf ew m ∈ caseSet ew) ∧
                                        (∀ ew ∈
                                            doubledBoxOriginIncidentEdges n,
                                          ∀ m ∈ Ωtouch,
                                            β *
                                              doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                                                β n v w e0 m ≤
                                              rowBoundEmptyIn ew
                                                (caseOf ew m)) ∧
                                          (∀ ew ∈
                                              doubledBoxOriginIncidentEdges n,
                                            ∀ m ∈ Ωtouch,
                                              β *
                                                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                                                  β n v w e0 m ≤
                                                rowBoundEmptyOutside ew
                                                  (caseOf ew m)) ∧
                                            (∀ ew ∈
                                                doubledBoxOriginIncidentEdges n,
                                              ∀ m ∈ Ωtouch,
                                                β *
                                                  doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                                                    β n v w e0 m ≤
                                                  rowBoundInnerIn ew
                                                    (caseOf ew m)) ∧
                                              (∀ ew ∈
                                                  doubledBoxOriginIncidentEdges
                                                    n,
                                                ∀ m ∈ Ωtouch,
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
                                                                Ωtouch
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
                                                                  Ωtouch
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                (∑ m ∈ Ωtouch,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v w e0 m) ≤
                    (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum
                      β n v) /
                      6 ∧
                  (∑ m ∈ Ωtouch,
                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                      β n v w e0 m) ≤
                    (β *
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n w)
                        (doubledBoxInnerPairSource n v w)) /
                      6

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                (∑ m ∈ Ωtouch,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v w e0 m) ≤
                    (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum
                      β n v) /
                      6

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                (∑ m ∈ Ωtouch,
                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                    β n v w e0 m) ≤
                    (β *
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n w)
                        (doubledBoxInnerPairSource n v w)) /
                      6

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ rowBudget : Profile → ℝ,
                  (∀ m ∈ Ωtouch,
                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                      β n v w e0 m ≤ rowBudget m) ∧
                    (∑ m ∈ Ωtouch, rowBudget m) ≤
                      (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum
                        β n v) /
                        6

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ rowBudget : Profile → ℝ,
                  (∀ m ∈ Ωtouch,
                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                      β n v w e0 m ≤ rowBudget m) ∧
                    (∑ m ∈ Ωtouch, rowBudget m) ≤
                      (β *
                        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                          (fun _ => 1)
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w)) /
                        6

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ rowCharge : Profile → ℝ,
                  (∀ m ∈ Ωtouch,
                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                      β n v w e0 m ≤ (β / 6) * rowCharge m) ∧
                    (∑ m ∈ Ωtouch, rowCharge m) ≤
                      doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ rowCharge : Profile → ℝ,
                  (∀ m ∈ Ωtouch,
                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                      β n v w e0 m ≤ (β / 6) * rowCharge m) ∧
                    (∑ m ∈ Ωtouch, rowCharge m) ≤
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n w)
                        (doubledBoxInnerPairSource n v w)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ route : Profile → Profile,
                  Set.InjOn route Ωtouch ∧
                    ∀ m ∈ Ωtouch,
                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                        β n v w e0 m ≤
                        (β / 6) *
                          edgeCopySourcePairSummand
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (doubledBoxOriginToInnerEndpointSource n v)
                            (∅ : Finset (FK.boxVerts 3 (2 * n)))
                            (route m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ route : Profile → Profile,
                  Set.InjOn route Ωtouch ∧
                    ∀ m ∈ Ωtouch,
                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                        β n v w e0 m ≤
                        (β / 6) *
                          edgeCopySourcePairSummand
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (doubledBoxOriginToInnerEndpointSource n w)
                            (doubledBoxInnerPairSource n v w)
                            (route m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumSourcePairInjectionChargeBoundsAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ route : Profile →
                    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                      (doubledBoxOriginToInnerEndpointSource n v)
                      (∅ : Finset (FK.boxVerts 3 (2 * n))),
                  Set.InjOn route Ωtouch ∧
                    ∀ m ∈ Ωtouch,
                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                        β n v w e0 m ≤
                        (β / 6) *
                          edgeCopySourcePairDataWeight
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (route m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
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
                let Ωtouch : Finset Profile :=
                  (Ω.filter
                    (doubledBoxIncrementedFullSourceActive n w e0)).filter
                    (fun m => doubledBoxOriginTouchesEdgeSupport n m)
                ∃ route : Profile →
                    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                      (doubledBoxOriginToInnerEndpointSource n w)
                      (doubledBoxInnerPairSource n v w),
                  Set.InjOn route Ωtouch ∧
                    ∀ m ∈ Ωtouch,
                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                        β n v w e0 m ≤
                        (β / 6) *
                          edgeCopySourcePairDataWeight
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (route m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    (β : ℝ) (n : ℕ)
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)] : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
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
                let Ωactive : Finset Profile :=
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ route : Profile →
                    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                      (doubledBoxOriginToInnerEndpointSource n v)
                      (∅ : Finset (FK.boxVerts 3 (2 * n))),
                  Set.InjOn route Ωactive ∧
                    ∀ m ∈ Ωactive,
                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                        β n v w e0 m ≤
                        (β / 6) *
                          edgeCopySourcePairDataWeight
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (route m)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
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
                let Ωactive : Finset Profile :=
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ route : Profile →
                    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                      (doubledBoxOriginToInnerEndpointSource n w)
                      (doubledBoxInnerPairSource n v w),
                  Set.InjOn route Ωactive ∧
                    ∀ m ∈ Ωactive,
                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                        β n v w e0 m ≤
                        (β / 6) *
                          edgeCopySourcePairDataWeight
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (route m)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n

end Exact3D
end StatMech
