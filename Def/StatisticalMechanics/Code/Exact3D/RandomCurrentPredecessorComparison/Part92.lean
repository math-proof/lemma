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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part99
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonUpdateSelectedEdgeMultiplicityFilterRouteBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  (∀ v : FK.boxVerts 3 n,
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
                ∃ route : Edge → Profile →
                    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                      (doubledBoxOriginToInnerEndpointSource n v)
                      (∅ : Finset (FK.boxVerts 3 (2 * n))),
                  (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                    Set.InjOn (route ew)
                      (Ωactive.filter
                        (fun m =>
                          (Function.update m e0 (m e0 + 1)) ew ≠ 0))) ∧
                    (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                      ∀ m ∈ Ωactive.filter
                          (fun m =>
                            (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                        doubledBoxOriginIncidentSupport n
                          (route ew m).1 = {ew}) ∧
                      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        ∀ m ∈ Ωactive.filter
                            (fun m =>
                              (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                            β n v w e0 m ≤
                            (β / 6) *
                              edgeCopySourcePairDataWeight
                                (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                (route ew m)) ∧
  (∀ v : FK.boxVerts 3 n,
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
                ∃ route : Edge → Profile →
                    edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                      (doubledBoxOriginToInnerEndpointSource n
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                      (doubledBoxInnerPairSource n v
                        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)),
                  (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                    Set.InjOn (route ew)
                      (Ωactive.filter
                        (fun m =>
                          (Function.update m e0 (m e0 + 1)) ew ≠ 0))) ∧
                    (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                      ∀ m ∈ Ωactive.filter
                          (fun m =>
                            (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                        doubledBoxOriginIncidentSupport n
                          (route ew m).1 = {ew}) ∧
                      ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        ∀ m ∈ Ωactive.filter
                            (fun m =>
                              (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                            β n v w e0 m ≤
                            (β / 6) *
                              edgeCopySourcePairDataWeight
                                (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                (route ew m))

end Exact3D
end StatMech
