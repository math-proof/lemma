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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part113
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def ExactSupportOwnerResidualSourcePairRouteShareBoundsAt
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
                let supportPatterns : Finset (Finset Edge) :=
                  Finset.filter (fun S => S.Nonempty)
                    (Finset.powerset (doubledBoxOriginIncidentEdges n))
                (∀ S ∈ supportPatterns,
                  ∀ ew ∈ S,
                    ∃ route : Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      Set.InjOn route
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S ∧
                                doubledBoxOriginIncidentOwner n m =
                                  some ew)) ∧
                        ∀ m ∈ Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S ∧
                                doubledBoxOriginIncidentOwner n m =
                                  some ew),
                          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                            β n v w e0 m ≤
                            ((β / 6) *
                              edgeCopySourcePairDataWeight
                                (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                (route m)) /
                              384) ∧
                  (∀ S ∈ supportPatterns,
                    ∀ ew ∈ S,
                      ∃ route : Profile →
                          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                            (doubledBoxOriginToInnerEndpointSource n w)
                            (doubledBoxInnerPairSource n v w),
                        Set.InjOn route
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S ∧
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew)) ∧
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S ∧
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
                            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                              β n v w e0 m ≤
                              ((β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route m)) /
                                384)

open Classical in
set_option linter.style.longLine false in


def ExactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt
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
                let supportPatterns : Finset (Finset Edge) :=
                  Finset.filter (fun S => S.Nonempty)
                    (Finset.powerset (doubledBoxOriginIncidentEdges n))
                (∀ S ∈ supportPatterns,
                  ∀ ew ∈ S,
                    ∃ profileRoute : Profile → Profile,
                      ∃ witness :
                          (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m)),
                        Set.InjOn profileRoute
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S ∧
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew)) ∧
                          (∀ m,
                            witness m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))
                                (profileRoute m)) ∧
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S ∧
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                ((β / 6) *
                                  Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                                    (fun _ => 1)
                                    (Sharpness.ofEdgeFun
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute m))) /
                                  384) ∧
                  (∀ S ∈ supportPatterns,
                    ∀ ew ∈ S,
                      ∃ profileRoute : Profile → Profile,
                        ∃ witness :
                            (m : Profile) →
                              Finset
                                (Sharpness.FluxEdgeCopy.Copy
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m)),
                          Set.InjOn profileRoute
                              (Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S ∧
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew)) ∧
                            (∀ m,
                              witness m ∈
                                edgeCopySourcePairWitnesses
                                  (FK.boxGraph 3 (2 * n))
                                  (doubledBoxOriginToInnerEndpointSource n w)
                                  (doubledBoxInnerPairSource n v w)
                                  (profileRoute m)) ∧
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S ∧
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                  β n v w e0 m ≤
                                  ((β / 6) *
                                    Sharpness.weight
                                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                      (Sharpness.ofEdgeFun
                                        (FK.boxGraph 3 (2 * n))
                                        (profileRoute m))) /
                                    384)

end Exact3D
end StatMech
