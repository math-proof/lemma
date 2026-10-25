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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part137
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonPredicateActiveRelaxedExplicitCaseTableBoundsAt
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
                          ∃ emptyRowBound : κ → ℝ,
                            ∃ emptyRelaxedBudget : κ → ℝ,
                              ∃ innerRowBound : κ → ℝ,
                                ∃ innerRelaxedBudget : κ → ℝ,
                                  (∀ m ∈ Ω, ¬ active m →
                                    doubledBoxSourceSectorResidualMomentEmptyBranchSummand
                                      β n v
                                      (boxVertStrictSectorYPredecessor3 v
                                        hvwedge hlt hypos)
                                      e0 m = 0) ∧
                                    (∀ m ∈ Ω, ¬ active m →
                                      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand
                                        β n v
                                        (boxVertStrictSectorYPredecessor3 v
                                          hvwedge hlt hypos)
                                        e0 m = 0) ∧
                                      (∀ m ∈ Ω.filter active,
                                        caseOf m ∈ caseSet) ∧
                                        (∀ m ∈ Ω.filter active,
                                          doubledBoxSourceSectorResidualMomentEmptyBranchSummand
                                            β n v
                                            (boxVertStrictSectorYPredecessor3
                                              v hvwedge hlt hypos)
                                            e0 m ≤
                                            emptyRowBound (caseOf m)) ∧
                                          (∀ m ∈ Ω.filter active,
                                            doubledBoxSourceSectorResidualMomentInnerPairBranchSummand
                                              β n v
                                              (boxVertStrictSectorYPredecessor3
                                                v hvwedge hlt hypos)
                                              e0 m ≤
                                              innerRowBound (caseOf m)) ∧
                                            (∀ c ∈ caseSet,
                                              emptyRowBound c ≤
                                                emptyRelaxedBudget c) ∧
                                              (∀ c ∈ caseSet,
                                                innerRowBound c ≤
                                                  innerRelaxedBudget c) ∧
                                                finiteSupportExplicitCaseBudgetTotal
                                                    (Ω.filter active) caseOf
                                                    caseSet
                                                    emptyRelaxedBudget ≤
                                                  β *
                                                    doubledBoxOriginToInnerEndpointSourcePairEmptySum
                                                      β n v ∧
                                                  finiteSupportExplicitCaseBudgetTotal
                                                      (Ω.filter active)
                                                      caseOf caseSet
                                                      innerRelaxedBudget ≤
                                                    β *
                                                      Sharpness.sourcePairSum
                                                        (FK.boxGraph 3
                                                          (2 * n))
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
