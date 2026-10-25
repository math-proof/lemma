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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part122
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentUpdateSelectedEdgeMultiplicityIndependentBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
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
                ∃ κEmptyIn : Type,
                  ∃ κEmptyOutside : Type,
                    ∃ κInnerIn : Type,
                      ∃ κInnerOutside : Type,
                        ∃ emptyInCaseSet : Edge → Finset κEmptyIn,
                          ∃ emptyInCaseOf : Edge → Profile → κEmptyIn,
                            ∃ emptyInRowBound : Edge → κEmptyIn → ℝ,
                              ∃ emptyInRelaxedBudget :
                                Edge → κEmptyIn → ℝ,
                                ∃ emptyOutsideCaseSet :
                                  Edge → Finset κEmptyOutside,
                                  ∃ emptyOutsideCaseOf :
                                    Edge → Profile → κEmptyOutside,
                                    ∃ emptyOutsideRowBound :
                                      Edge → κEmptyOutside → ℝ,
                                      ∃ emptyOutsideRelaxedBudget :
                                        Edge → κEmptyOutside → ℝ,
                                        ∃ innerInCaseSet :
                                          Edge → Finset κInnerIn,
                                          ∃ innerInCaseOf :
                                            Edge → Profile → κInnerIn,
                                            ∃ innerInRowBound :
                                              Edge → κInnerIn → ℝ,
                                              ∃ innerInRelaxedBudget :
                                                Edge → κInnerIn → ℝ,
                                                ∃ innerOutsideCaseSet :
                                                  Edge →
                                                    Finset κInnerOutside,
                                                  ∃ innerOutsideCaseOf :
                                                    Edge → Profile →
                                                      κInnerOutside,
                                                    ∃ innerOutsideRowBound :
                                                      Edge →
                                                        κInnerOutside → ℝ,
                                                      ∃ innerOutsideRelaxedBudget :
                                                        Edge →
                                                          κInnerOutside → ℝ,
                                                        (∀ ew ∈
                                                            doubledBoxOriginIncidentEdges
                                                              n,
                                                          ∀ m ∈ Ωupdate ew,
                                                            emptyInCaseOf ew m ∈
                                                              emptyInCaseSet
                                                                ew) ∧
                                                          (∀ ew ∈
                                                              doubledBoxOriginIncidentEdges
                                                                n,
                                                            ∀ m ∈ Ωupdate ew,
                                                              emptyOutsideCaseOf
                                                                  ew m ∈
                                                                emptyOutsideCaseSet
                                                                  ew) ∧
                                                            (∀ ew ∈
                                                                doubledBoxOriginIncidentEdges
                                                                  n,
                                                              ∀ m ∈ Ωupdate ew,
                                                                innerInCaseOf
                                                                    ew m ∈
                                                                  innerInCaseSet
                                                                    ew) ∧
                                                              (∀ ew ∈
                                                                  doubledBoxOriginIncidentEdges
                                                                    n,
                                                                ∀ m ∈
                                                                    Ωupdate
                                                                      ew,
                                                                  innerOutsideCaseOf
                                                                      ew m ∈
                                                                    innerOutsideCaseSet
                                                                      ew) ∧
                                                                (∀ ew ∈
                                                                    doubledBoxOriginIncidentEdges
                                                                      n,
                                                                  ∀ m ∈
                                                                      Ωupdate
                                                                        ew,
                                                                    β *
                                                                      doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                                                                        β n v
                                                                        w e0
                                                                        m ≤
                                                                      emptyInRowBound
                                                                        ew
                                                                        (emptyInCaseOf
                                                                          ew
                                                                          m)) ∧
                                                                  (∀ ew ∈
                                                                      doubledBoxOriginIncidentEdges
                                                                        n,
                                                                    ∀ m ∈
                                                                        Ωupdate
                                                                          ew,
                                                                      β *
                                                                        doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                                                                          β n
                                                                          v w
                                                                          e0
                                                                          m ≤
                                                                        emptyOutsideRowBound
                                                                          ew
                                                                          (emptyOutsideCaseOf
                                                                            ew
                                                                            m)) ∧
                                                                    (∀ ew ∈
                                                                        doubledBoxOriginIncidentEdges
                                                                          n,
                                                                      ∀ m ∈
                                                                          Ωupdate
                                                                            ew,
                                                                        β *
                                                                          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                                                                            β
                                                                            n
                                                                            v
                                                                            w
                                                                            e0
                                                                            m ≤
                                                                          innerInRowBound
                                                                            ew
                                                                            (innerInCaseOf
                                                                              ew
                                                                              m)) ∧
                                                                      (∀ ew ∈
                                                                          doubledBoxOriginIncidentEdges
                                                                            n,
                                                                        ∀ m ∈
                                                                            Ωupdate
                                                                              ew,
                                                                          β *
                                                                            doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                                                                              β
                                                                              n
                                                                              v
                                                                              w
                                                                              e0
                                                                              m ≤
                                                                            innerOutsideRowBound
                                                                              ew
                                                                              (innerOutsideCaseOf
                                                                                ew
                                                                                m)) ∧
                                                                        (∀ ew ∈
                                                                            doubledBoxOriginIncidentEdges
                                                                              n,
                                                                          ∀ c ∈
                                                                              emptyInCaseSet
                                                                                ew,
                                                                            emptyInRowBound
                                                                                ew
                                                                                c ≤
                                                                              emptyInRelaxedBudget
                                                                                ew
                                                                                c) ∧
                                                                          (∀ ew ∈
                                                                              doubledBoxOriginIncidentEdges
                                                                                n,
                                                                            ∀ c ∈
                                                                                emptyOutsideCaseSet
                                                                                  ew,
                                                                              emptyOutsideRowBound
                                                                                  ew
                                                                                  c ≤
                                                                                emptyOutsideRelaxedBudget
                                                                                  ew
                                                                                  c) ∧
                                                                            (∀ ew ∈
                                                                                doubledBoxOriginIncidentEdges
                                                                                  n,
                                                                              ∀ c ∈
                                                                                  innerInCaseSet
                                                                                    ew,
                                                                                innerInRowBound
                                                                                    ew
                                                                                    c ≤
                                                                                  innerInRelaxedBudget
                                                                                    ew
                                                                                    c) ∧
                                                                              (∀ ew ∈
                                                                                  doubledBoxOriginIncidentEdges
                                                                                    n,
                                                                                ∀ c ∈
                                                                                    innerOutsideCaseSet
                                                                                      ew,
                                                                                  innerOutsideRowBound
                                                                                      ew
                                                                                      c ≤
                                                                                    innerOutsideRelaxedBudget
                                                                                      ew
                                                                                      c) ∧
                                                                                (∀ ew ∈
                                                                                    doubledBoxOriginIncidentEdges
                                                                                      n,
                                                                                  ∀ cin ∈
                                                                                      emptyInCaseSet
                                                                                        ew,
                                                                                    ∀ cout ∈
                                                                                        emptyOutsideCaseSet
                                                                                          ew,
                                                                                      0 ≤
                                                                                        emptyInRelaxedBudget
                                                                                            ew
                                                                                            cin +
                                                                                          emptyOutsideRelaxedBudget
                                                                                            ew
                                                                                            cout) ∧
                                                                                  (∀ ew ∈
                                                                                      doubledBoxOriginIncidentEdges
                                                                                        n,
                                                                                    ∀ cin ∈
                                                                                        innerInCaseSet
                                                                                          ew,
                                                                                      ∀ cout ∈
                                                                                          innerOutsideCaseSet
                                                                                            ew,
                                                                                        0 ≤
                                                                                          innerInRelaxedBudget
                                                                                              ew
                                                                                              cin +
                                                                                            innerOutsideRelaxedBudget
                                                                                              ew
                                                                                              cout) ∧
                                                                                    (∀ ew ∈
                                                                                        doubledBoxOriginIncidentEdges
                                                                                          n,
                                                                                      finiteSupportExplicitCaseBudgetTotal
                                                                                          (Ωupdate
                                                                                            ew)
                                                                                          (emptyInCaseOf
                                                                                            ew)
                                                                                          (emptyInCaseSet
                                                                                            ew)
                                                                                          (emptyInRelaxedBudget
                                                                                            ew) +
                                                                                        finiteSupportExplicitCaseBudgetTotal
                                                                                          (Ωupdate
                                                                                            ew)
                                                                                          (emptyOutsideCaseOf
                                                                                            ew)
                                                                                          (emptyOutsideCaseSet
                                                                                            ew)
                                                                                          (emptyOutsideRelaxedBudget
                                                                                            ew) ≤
                                                                                        (β *
                                                                                          doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                                                                            β
                                                                                            n
                                                                                            v) /
                                                                                          6) ∧
                                                                                      (∀ ew ∈
                                                                                        doubledBoxOriginIncidentEdges
                                                                                          n,
                                                                                        finiteSupportExplicitCaseBudgetTotal
                                                                                            (Ωupdate
                                                                                              ew)
                                                                                            (innerInCaseOf
                                                                                              ew)
                                                                                            (innerInCaseSet
                                                                                              ew)
                                                                                            (innerInRelaxedBudget
                                                                                              ew) +
                                                                                          finiteSupportExplicitCaseBudgetTotal
                                                                                            (Ωupdate
                                                                                              ew)
                                                                                            (innerOutsideCaseOf
                                                                                              ew)
                                                                                            (innerOutsideCaseSet
                                                                                              ew)
                                                                                            (innerOutsideRelaxedBudget
                                                                                              ew) ≤
                                                                                          (β *
                                                                                            Sharpness.sourcePairSum
                                                                                              (FK.boxGraph
                                                                                                3
                                                                                                (2 *
                                                                                                  n))
                                                                                              β
                                                                                              (fun _ =>
                                                                                                1)
                                                                                              (doubledBoxOriginToInnerEndpointSource
                                                                                                n
                                                                                                w)
                                                                                              (doubledBoxInnerPairSource
                                                                                                n
                                                                                                v
                                                                                                w)) /
                                                                                            6)

end Exact3D
end StatMech
