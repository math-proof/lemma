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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part93
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt_of_empty_inner_multiplicityFilterRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
      β n :=
  ⟨hempty, hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_multiplicityFilterRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n :=
  hroute.1

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_multiplicityFilterRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n :=
  hroute.2

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_profileWitness_routes
    {β : ℝ} {n : ℕ}
    (hroute :
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
                      Ω.filter
                        (doubledBoxIncrementedFullSourceActive n w e0)
                    ∃ profileRoute : Edge → Profile → Profile,
                      ∃ witness :
                          (ew : Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute ew m)),
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          Set.InjOn (profileRoute ew)
                            (Ωactive.filter (fun m => m ew ≠ 0))) ∧
                          (∀ ew m,
                            witness ew m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))
                                (profileRoute ew m)) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈
                                  Ωactive.filter (fun m => m ew ≠ 0),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute ew m) = {ew}) ∧
                              ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n := by
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos w e0 hedge Ω
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, w] using
    edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_profileWitness_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hwitness hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_profileWitness_routes
    {β : ℝ} {n : ℕ}
    (hroute :
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
                      Ω.filter
                        (doubledBoxIncrementedFullSourceActive n w e0)
                    ∃ profileRoute : Edge → Profile → Profile,
                      ∃ witness :
                          (ew : Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute ew m)),
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          Set.InjOn (profileRoute ew)
                            (Ωactive.filter (fun m => m ew ≠ 0))) ∧
                          (∀ ew m,
                            witness ew m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n w)
                                (doubledBoxInnerPairSource n v w)
                                (profileRoute ew m)) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈
                                  Ωactive.filter (fun m => m ew ≠ 0),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute ew m) = {ew}) ∧
                              ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n := by
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos w e0 hedge Ω
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, w] using
    edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_profileWitness_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hwitness hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_sourceEquation_routes
    {β : ℝ} {n : ℕ}
    (hroute :
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
                      Ω.filter
                        (doubledBoxIncrementedFullSourceActive n w e0)
                    ∃ profileRoute : Edge → Profile → Profile,
                      ∃ witness :
                          (ew : Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute ew m)),
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          Set.InjOn (profileRoute ew)
                            (Ωactive.filter (fun m => m ew ≠ 0))) ∧
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
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute ew m) = {ew}) ∧
                                ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈
                                      Ωactive.filter (fun m => m ew ≠ 0),
                                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                      β n v w e0 m ≤
                                      (β / 6) *
                                        Sharpness.weight
                                          (FK.boxGraph 3 (2 * n)) β
                                          (fun _ => 1)
                                          (Sharpness.ofEdgeFun
                                            (FK.boxGraph 3 (2 * n))
                                            (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n := by
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos w e0 hedge Ω
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hleft, hright, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, w] using
    edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_sourceEquation_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hleft hright hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_sourceEquation_routes
    {β : ℝ} {n : ℕ}
    (hroute :
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
                      Ω.filter
                        (doubledBoxIncrementedFullSourceActive n w e0)
                    ∃ profileRoute : Edge → Profile → Profile,
                      ∃ witness :
                          (ew : Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute ew m)),
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          Set.InjOn (profileRoute ew)
                            (Ωactive.filter (fun m => m ew ≠ 0))) ∧
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
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute ew m) = {ew}) ∧
                                ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈
                                      Ωactive.filter (fun m => m ew ≠ 0),
                                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                      β n v w e0 m ≤
                                      (β / 6) *
                                        Sharpness.weight
                                          (FK.boxGraph 3 (2 * n)) β
                                          (fun _ => 1)
                                          (Sharpness.ofEdgeFun
                                            (FK.boxGraph 3 (2 * n))
                                            (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n := by
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos w e0 hedge Ω
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hleft, hright, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, w] using
    edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_sourceEquation_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hleft hright hinj hsupport hpoint

end Exact3D
end StatMech
