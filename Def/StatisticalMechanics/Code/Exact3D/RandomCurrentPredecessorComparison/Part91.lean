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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part98
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
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
                ∃ profileRoute : Edge → Profile → Profile,
                  ∃ witness :
                      (ew : Edge) → (m : Profile) →
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n))
                            (profileRoute ew m)),
                    (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                      Set.InjOn (profileRoute ew)
                        (Ωactive.filter
                          (fun m =>
                            doubledBoxOriginIncidentOwner n m = some ew))) ∧
                      (∀ ew m,
                        Sharpness.RandomCurrent.sources
                          (Sharpness.FluxEdgeCopy.endsM
                            (FK.boxGraph 3 (2 * n))
                            (profileRoute ew m))
                          (witness ew m) =
                          doubledBoxOriginToInnerEndpointSource n v) ∧
                        (∀ ew m,
                          Sharpness.RandomCurrent.sources
                            (Sharpness.FluxEdgeCopy.endsM
                              (FK.boxGraph 3 (2 * n))
                              (profileRoute ew m))
                            ((Finset.univ :
                                Finset
                                  (Sharpness.FluxEdgeCopy.Copy
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute ew m))) \
                              witness ew m) =
                            (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                          (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈
                                Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                              doubledBoxOriginIncidentSupport n
                                (profileRoute ew m) = {ew}) ∧
                            ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈
                                  Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                  β n v w e0 m ≤
                                  (β / 6) *
                                    Sharpness.weight
                                      (FK.boxGraph 3 (2 * n)) β
                                      (fun _ => 1)
                                      (Sharpness.ofEdgeFun
                                        (FK.boxGraph 3 (2 * n))
                                        (profileRoute ew m))

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
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
                ∃ profileRoute : Edge → Profile → Profile,
                  ∃ witness :
                      (ew : Edge) → (m : Profile) →
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n))
                            (profileRoute ew m)),
                    (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                      Set.InjOn (profileRoute ew)
                        (Ωactive.filter
                          (fun m =>
                            doubledBoxOriginIncidentOwner n m = some ew))) ∧
                      (∀ ew m,
                        Sharpness.RandomCurrent.sources
                          (Sharpness.FluxEdgeCopy.endsM
                            (FK.boxGraph 3 (2 * n))
                            (profileRoute ew m))
                          (witness ew m) =
                          doubledBoxOriginToInnerEndpointSource n w) ∧
                        (∀ ew m,
                          Sharpness.RandomCurrent.sources
                            (Sharpness.FluxEdgeCopy.endsM
                              (FK.boxGraph 3 (2 * n))
                              (profileRoute ew m))
                            ((Finset.univ :
                                Finset
                                  (Sharpness.FluxEdgeCopy.Copy
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute ew m))) \
                              witness ew m) =
                            doubledBoxInnerPairSource n v w) ∧
                          (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈
                                Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                              doubledBoxOriginIncidentSupport n
                                (profileRoute ew m) = {ew}) ∧
                            ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈
                                  Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                  β n v w e0 m ≤
                                  (β / 6) *
                                    Sharpness.weight
                                      (FK.boxGraph 3 (2 * n)) β
                                      (fun _ => 1)
                                      (Sharpness.ofEdgeFun
                                        (FK.boxGraph 3 (2 * n))
                                        (profileRoute ew m))

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
      β n

end Exact3D
end StatMech
