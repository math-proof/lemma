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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part142
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
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
                ∃ active :
                  (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop,
                  ∃ hactive : DecidablePred active,
                    letI : DecidablePred active := hactive
                    ∃ κ : Type,
                      ∃ caseSet : Finset κ,
                        ∃ caseOf :
                          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ,
                          ∃ rowBound : κ → ℝ,
                            ∃ relaxedBudget : κ → ℝ,
                              (∀ m ∈ Ω, ¬ active m →
                                doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                  β n v
                                  (boxVertStrictSectorYPredecessor3 v hvwedge
                                    hlt hypos)
                                  e0 m = 0) ∧
                                (∀ m ∈ Ω.filter active,
                                  caseOf m ∈ caseSet) ∧
                                  (∀ m ∈ Ω.filter active,
                                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                      β n v
                                      (boxVertStrictSectorYPredecessor3 v
                                        hvwedge hlt hypos)
                                      e0 m ≤ rowBound (caseOf m)) ∧
                                    (∀ c ∈ caseSet,
                                      rowBound c ≤ relaxedBudget c) ∧
                                      finiteSupportExplicitCaseBudgetTotal
                                          (Ω.filter active) caseOf caseSet
                                          relaxedBudget ≤
                                        doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                          β n v

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
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
                ∃ active :
                  (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop,
                  ∃ hactive : DecidablePred active,
                    letI : DecidablePred active := hactive
                    ∃ κ : Type,
                      ∃ caseSet : Finset κ,
                        ∃ caseOf :
                          (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → κ,
                          ∃ rowBound : κ → ℝ,
                            ∃ relaxedBudget : κ → ℝ,
                              (∀ m ∈ Ω, ¬ active m →
                                doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                  β n v
                                  (boxVertStrictSectorYPredecessor3 v hvwedge
                                    hlt hypos)
                                  e0 m = 0) ∧
                                (∀ m ∈ Ω.filter active,
                                  caseOf m ∈ caseSet) ∧
                                  (∀ m ∈ Ω.filter active,
                                    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                      β n v
                                      (boxVertStrictSectorYPredecessor3 v
                                        hvwedge hlt hypos)
                                      e0 m ≤ rowBound (caseOf m)) ∧
                                    (∀ c ∈ caseSet,
                                      rowBound c ≤ relaxedBudget c) ∧
                                      finiteSupportExplicitCaseBudgetTotal
                                          (Ω.filter active) caseOf caseSet
                                          relaxedBudget ≤
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyEmptyFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyInnerPairFiniteCutoffPredicateActiveRelaxedExplicitCaseTableBoundAt
      β n

end Exact3D
end StatMech
