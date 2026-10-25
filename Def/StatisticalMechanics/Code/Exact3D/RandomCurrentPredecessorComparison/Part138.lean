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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part145
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
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
                ∃ κ : Type,
                  ∃ caseSet :
                    Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                      Finset κ,
                    ∃ caseOf :
                      Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ,
                      ∃ emptyRowBound :
                        Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                          κ → ℝ,
                        ∃ emptyRelaxedBudget :
                          Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                            κ → ℝ,
                          ∃ innerRowBound :
                            Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                              κ → ℝ,
                            ∃ innerRelaxedBudget :
                              Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset →
                                κ → ℝ,
                              (∀ S ∈
                                  Finset.filter (fun S => S.Nonempty)
                                    (Finset.powerset
                                      (doubledBoxOriginIncidentEdges n)),
                                ∀ m ∈ Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  caseOf S m ∈ caseSet S) ∧
                                (∀ S ∈
                                    Finset.filter (fun S => S.Nonempty)
                                      (Finset.powerset
                                        (doubledBoxOriginIncidentEdges n)),
                                  ∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                      β n v
                                      (boxVertStrictSectorYPredecessor3 v
                                        hvwedge hlt hypos)
                                      e0 m ≤
                                      emptyRowBound S (caseOf S m)) ∧
                                  (∀ S ∈
                                      Finset.filter (fun S => S.Nonempty)
                                        (Finset.powerset
                                          (doubledBoxOriginIncidentEdges n)),
                                    ∀ m ∈ Ω.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                        β n v
                                        (boxVertStrictSectorYPredecessor3 v
                                          hvwedge hlt hypos)
                                        e0 m ≤
                                        innerRowBound S (caseOf S m)) ∧
                                    (∀ S ∈
                                        Finset.filter (fun S => S.Nonempty)
                                          (Finset.powerset
                                            (doubledBoxOriginIncidentEdges n)),
                                      ∀ c ∈ caseSet S,
                                        emptyRowBound S c ≤
                                          emptyRelaxedBudget S c) ∧
                                      (∀ S ∈
                                          Finset.filter (fun S => S.Nonempty)
                                            (Finset.powerset
                                              (doubledBoxOriginIncidentEdges n)),
                                        ∀ c ∈ caseSet S,
                                          innerRowBound S c ≤
                                            innerRelaxedBudget S c) ∧
                                        (∑ S ∈
                                            Finset.filter
                                              (fun S => S.Nonempty)
                                              (Finset.powerset
                                                (doubledBoxOriginIncidentEdges
                                                  n)),
                                          finiteSupportExplicitCaseBudgetTotal
                                            (Ω.filter
                                              (fun m =>
                                                doubledBoxOriginIncidentSupport
                                                    n m =
                                                  S))
                                            (caseOf S) (caseSet S)
                                            (emptyRelaxedBudget S)) ≤
                                          doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                            β n v ∧
                                          (∑ S ∈
                                              Finset.filter
                                                (fun S => S.Nonempty)
                                                (Finset.powerset
                                                  (doubledBoxOriginIncidentEdges
                                                    n)),
                                            finiteSupportExplicitCaseBudgetTotal
                                              (Ω.filter
                                                (fun m =>
                                                  doubledBoxOriginIncidentSupport
                                                      n m =
                                                    S))
                                              (caseOf S) (caseSet S)
                                              (innerRelaxedBudget S)) ≤
                                            Sharpness.sourcePairSum
                                              (FK.boxGraph 3 (2 * n)) β
                                              (fun _ => 1)
                                              (doubledBoxOriginToInnerEndpointSource
                                                n
                                                (boxVertStrictSectorYPredecessor3
                                                  v hvwedge hlt hypos))
                                              (doubledBoxInnerPairSource n v
                                                (boxVertStrictSectorYPredecessor3
                                                  v hvwedge hlt hypos))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAt
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
                ∃ emptyBudget :
                  Finset Edge → Profile → ℝ,
                  ∃ innerBudget :
                    Finset Edge → Profile → ℝ,
                    (∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      ∀ m ∈ Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S),
                        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                          β n v w e0 m ≤ emptyBudget S m) ∧
                      (∀ S ∈
                          Finset.filter (fun S => S.Nonempty)
                            (Finset.powerset
                              (doubledBoxOriginIncidentEdges n)),
                        ∀ m ∈ Ω.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S),
                          doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                            β n v w e0 m ≤ innerBudget S m) ∧
                        (∑ S ∈
                            Finset.filter (fun S => S.Nonempty)
                              (Finset.powerset
                                (doubledBoxOriginIncidentEdges n)),
                          ∑ m ∈ Ω.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            emptyBudget S m) ≤
                          doubledBoxOriginToInnerEndpointSourcePairEmptySum
                            β n v ∧
                          (∑ S ∈
                              Finset.filter (fun S => S.Nonempty)
                                (Finset.powerset
                                  (doubledBoxOriginIncidentEdges n)),
                            ∑ m ∈ Ω.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              innerBudget S m) ≤
                            Sharpness.sourcePairSum
                              (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                              (doubledBoxOriginToInnerEndpointSource n w)
                              (doubledBoxInnerPairSource n v w)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAt
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
                ∃ emptyBudget :
                  Finset Edge → Profile → ℝ,
                  ∃ innerBudget :
                    Finset Edge → Profile → ℝ,
                    (∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      ∀ m ∈ Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S),
                        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                          β n v w e0 m ≤ emptyBudget S m) ∧
                      (∀ S ∈
                          Finset.filter (fun S => S.Nonempty)
                            (Finset.powerset
                              (doubledBoxOriginIncidentEdges n)),
                        ∀ m ∈ Ω.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S),
                          doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                            β n v w e0 m ≤ innerBudget S m) ∧
                        (∀ S ∈
                            Finset.filter (fun S => S.Nonempty)
                              (Finset.powerset
                                (doubledBoxOriginIncidentEdges n)),
                          (∑ m ∈ Ω.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            emptyBudget S m) ≤
                            doubledBoxOriginToInnerEndpointSourcePairEmptySum
                              β n v / 64) ∧
                          (∀ S ∈
                              Finset.filter (fun S => S.Nonempty)
                                (Finset.powerset
                                  (doubledBoxOriginIncidentEdges n)),
                            (∑ m ∈ Ω.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              innerBudget S m) ≤
                              Sharpness.sourcePairSum
                                (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                (doubledBoxOriginToInnerEndpointSource n w)
                                (doubledBoxInnerPairSource n v w) / 64)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
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
                ∃ emptyRoute : Finset Edge → Profile → Profile,
                  ∃ innerRoute : Finset Edge → Profile → Profile,
                    (∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      Set.InjOn (emptyRoute S)
                        (Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S))) ∧
                      (∀ S ∈
                          Finset.filter (fun S => S.Nonempty)
                            (Finset.powerset
                              (doubledBoxOriginIncidentEdges n)),
                        Set.InjOn (innerRoute S)
                          (Ω.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S))) ∧
                        (∀ S ∈
                            Finset.filter (fun S => S.Nonempty)
                              (Finset.powerset
                                (doubledBoxOriginIncidentEdges n)),
                          ∀ m ∈ Ω.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                              β n v w e0 m ≤
                              edgeCopySourcePairSummand
                                (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset
                                  (FK.boxVerts 3 (2 * n)))
                                (emptyRoute S m) / 64) ∧
                          (∀ S ∈
                              Finset.filter (fun S => S.Nonempty)
                                (Finset.powerset
                                  (doubledBoxOriginIncidentEdges n)),
                            ∀ m ∈ Ω.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                β n v w e0 m ≤
                                edgeCopySourcePairSummand
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (doubledBoxOriginToInnerEndpointSource n w)
                                  (doubledBoxInnerPairSource n v w)
                                  (innerRoute S m) / 64)

end Exact3D
end StatMech
