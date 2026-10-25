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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part94
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_pointwiseSourceEquationRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_sourceEquation_routes
    hroute

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_pointwiseSourceEquationRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_sourceEquation_routes
    hroute

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt_of_pointwiseSourceEquationRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterPointwiseSourceEquationRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_pointwiseSourceEquationRouteBoundAt
      hroute.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_pointwiseSourceEquationRouteBoundAt
      hroute.2⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_profileWitness_multiplicitySupport_routes
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
                                profileRoute ew m ew ≠ 0) ∧
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                    e ≠ ew → profileRoute ew m e = 0) ∧
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
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_profileWitness_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hpos, hzero, hpoint⟩
  refine ⟨profileRoute, witness, hinj, hwitness, ?_, hpoint⟩
  intro ew hew m hm
  exact
    doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
      (n := n) (m := profileRoute ew m) (ew := ew) hew
      (hpos ew hew m hm) (hzero ew hew m hm)

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_profileWitness_multiplicitySupport_routes
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
                                profileRoute ew m ew ≠ 0) ∧
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                    e ≠ ew → profileRoute ew m e = 0) ∧
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
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_profileWitness_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hpos, hzero, hpoint⟩
  refine ⟨profileRoute, witness, hinj, hwitness, ?_, hpoint⟩
  intro ew hew m hm
  exact
    doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
      (n := n) (m := profileRoute ew m) (ew := ew) hew
      (hpos ew hew m hm) (hzero ew hew m hm)

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt_of_forall_multiplicity_profileWitness_routes
    {β : ℝ} {n : ℕ}
    (hempty :
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
                                          (profileRoute ew m)))
    (hinner :
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
      β n := by
  classical
  constructor
  · dsimp only at hempty ⊢
    intro v hvwedge hlt hypos e0 hedge Ω
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let owners : Finset Edge := doubledBoxOriginIncidentEdges n
    let F : Profile → ℝ :=
      fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m
    rcases hempty v hvwedge hlt hypos e0 hedge Ω with
      ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
    simpa [F, Ωactive, owners, w] using
      edgeCopySourcePairData_positiveMultiplicityIndexed_routes_of_profileWitness_routes
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
        (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
        Ωactive owners (doubledBoxOriginIncidentSupport n) F
        profileRoute witness hwitness hinj hsupport hpoint
  · dsimp only at hinner ⊢
    intro v hvwedge hlt hypos e0 hedge Ω
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let owners : Finset Edge := doubledBoxOriginIncidentEdges n
    let F : Profile → ℝ :=
      fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m
    rcases hinner v hvwedge hlt hypos e0 hedge Ω with
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
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt_of_forall_multiplicity_sourceEquation_routes
    {β : ℝ} {n : ℕ}
    (hempty :
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
                                            (profileRoute ew m)))
    (hinner :
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_sourceEquation_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundAt_of_forall_multiplicity_sourceEquation_routes
      hinner⟩

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt_of_forall_multiplicity_profileWitness_multiplicitySupport_routes
    {β : ℝ} {n : ℕ}
    (hempty :
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
                                profileRoute ew m ew ≠ 0) ∧
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                    e ≠ ew → profileRoute ew m e = 0) ∧
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
                                            (profileRoute ew m)))
    (hinner :
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
                                profileRoute ew m ew ≠ 0) ∧
                              (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                ∀ m ∈
                                    Ωactive.filter (fun m => m ew ≠ 0),
                                  ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                    e ≠ ew → profileRoute ew m e = 0) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt_of_forall_multiplicity_profileWitness_routes
      ?_ ?_
  · dsimp only at hempty ⊢
    intro v hvwedge hlt hypos e0 hedge Ω
    rcases hempty v hvwedge hlt hypos e0 hedge Ω with
      ⟨profileRoute, witness, hinj, hwitness, hpos, hzero, hpoint⟩
    refine ⟨profileRoute, witness, hinj, hwitness, ?_, hpoint⟩
    intro ew hew m hm
    exact
      doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
        (n := n) (m := profileRoute ew m) (ew := ew) hew
        (hpos ew hew m hm) (hzero ew hew m hm)
  · dsimp only at hinner ⊢
    intro v hvwedge hlt hypos e0 hedge Ω
    rcases hinner v hvwedge hlt hypos e0 hedge Ω with
      ⟨profileRoute, witness, hinj, hwitness, hpos, hzero, hpoint⟩
    refine ⟨profileRoute, witness, hinj, hwitness, ?_, hpoint⟩
    intro ew hew m hm
    exact
      doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
        (n := n) (m := profileRoute ew m) (ew := ew) hew
        (hpos ew hew m hm) (hzero ew hew m hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonUpdateSelectedEdgeMultiplicityFilterRouteBoundsAt_of_multiplicityFilterRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonUpdateSelectedEdgeMultiplicityFilterRouteBoundsAt
      β n := by
  classical
  rcases hroute with ⟨hempty, hinner⟩
  constructor
  · intro v hvwedge hlt hypos
    dsimp only
    intro e0 hedge Ω
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    rcases hempty v hvwedge hlt hypos e0 hedge Ω with
      ⟨route, hinj, hsupport, hpoint⟩
    refine ⟨route, ?_, ?_, ?_⟩
    · intro ew hew a ha b hb hroute_eq
      have hfilter :
          Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
            Ωactive.filter (fun m => m ew ≠ 0) := by
        simpa [Ωactive, w] using
          doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            hew (by simpa [w] using hedge) Ωactive
      exact hinj ew hew (by rw [← hfilter]; exact ha)
        (by rw [← hfilter]; exact hb) hroute_eq
    · intro ew hew m hm
      have hfilter :
          Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
            Ωactive.filter (fun m => m ew ≠ 0) := by
        simpa [Ωactive, w] using
          doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            hew (by simpa [w] using hedge) Ωactive
      exact hsupport ew hew m (by rw [← hfilter]; exact hm)
    · intro ew hew m hm
      have hfilter :
          Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
            Ωactive.filter (fun m => m ew ≠ 0) := by
        simpa [Ωactive, w] using
          doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            hew (by simpa [w] using hedge) Ωactive
      exact hpoint ew hew m (by rw [← hfilter]; exact hm)
  · intro v hvwedge hlt hypos
    dsimp only
    intro e0 hedge Ω
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive :
        Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    rcases hinner v hvwedge hlt hypos e0 hedge Ω with
      ⟨route, hinj, hsupport, hpoint⟩
    refine ⟨route, ?_, ?_, ?_⟩
    · intro ew hew a ha b hb hroute_eq
      have hfilter :
          Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
            Ωactive.filter (fun m => m ew ≠ 0) := by
        simpa [Ωactive, w] using
          doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            hew (by simpa [w] using hedge) Ωactive
      exact hinj ew hew (by rw [← hfilter]; exact ha)
        (by rw [← hfilter]; exact hb) hroute_eq
    · intro ew hew m hm
      have hfilter :
          Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
            Ωactive.filter (fun m => m ew ≠ 0) := by
        simpa [Ωactive, w] using
          doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            hew (by simpa [w] using hedge) Ωactive
      exact hsupport ew hew m (by rw [← hfilter]; exact hm)
    · intro ew hew m hm
      have hfilter :
          Ωactive.filter
              (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) =
            Ωactive.filter (fun m => m ew ≠ 0) := by
        simpa [Ωactive, w] using
          doubledBoxUpdateSelectedEdgeMultiplicity_filter_eq_multiplicity_filter_of_strictSectorYPredecessor3
            (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
            hew (by simpa [w] using hedge) Ωactive
      exact hpoint ew hew m (by rw [← hfilter]; exact hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_multiplicityFilterRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonMultiplicityFilterRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_updateSelectedEdgeMultiplicityFilterRouteBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonUpdateSelectedEdgeMultiplicityFilterRouteBoundsAt_of_multiplicityFilterRouteBoundsAt
      hroute)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hsupportSingleton :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases hsupportSingleton v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, hinj, hsupport, hpoint⟩
  refine ⟨ownerOf, howner, route, hinj, ?_, hpoint⟩
  intro ew hew m hm
  exact
    doubledBoxOriginIncidentOwner_eq_some_of_originIncidentSupport_eq_singleton
      (n := n) (m := (route ew m).1) (ew := ew)
      (hsupport ew hew m hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hsupportSingleton :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases hsupportSingleton v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, hinj, hsupport, hpoint⟩
  refine ⟨ownerOf, howner, route, hinj, ?_, hpoint⟩
  intro ew hew m hm
  exact
    doubledBoxOriginIncidentOwner_eq_some_of_originIncidentSupport_eq_singleton
      (n := n) (m := (route ew m).1) (ew := ew)
      (hsupport ew hew m hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hsupportSingleton :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      hsupportSingleton.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      hsupportSingleton.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hprofileTagged :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases hprofileTagged v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, hinj, hprofileOwner, hpoint⟩
  refine
    ⟨ownerOf, howner, route,
      edgeCopySourcePairDataOriginIncidentOwnerTag (n := n)
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (B := (∅ : Finset (FK.boxVerts 3 (2 * n)))) e0,
      hinj, ?_, hpoint⟩
  intro ew hew m hm
  exact
    edgeCopySourcePairDataOriginIncidentOwnerTag_eq_of_profile_owner_eq_some
      (n := n)
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      e0 ew (route ew m) (hprofileOwner ew hew m hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hprofileTagged :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  rcases hprofileTagged v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, hinj, hprofileOwner, hpoint⟩
  refine
    ⟨ownerOf, howner, route,
      edgeCopySourcePairDataOriginIncidentOwnerTag (n := n)
        (A := doubledBoxOriginToInnerEndpointSource n w)
        (B := doubledBoxInnerPairSource n v w) e0,
      hinj, ?_, hpoint⟩
  intro ew hew m hm
  exact
    edgeCopySourcePairDataOriginIncidentOwnerTag_eq_of_profile_owner_eq_some
      (n := n)
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      e0 ew (route ew m) (hprofileOwner ew hew m hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hprofileTagged :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
      hprofileTagged.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
      hprofileTagged.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
    {β : ℝ} {n : ℕ}
    (htagged :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases htagged v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, tag, hinj, htag, hpoint⟩
  refine ⟨ownerOf, howner, route, hinj, ?_, hpoint⟩
  intro ew hew ew' hew' hne m hm m' hm' hroute
  have htag_eq : tag (route ew m) = tag (route ew' m') :=
    congrArg tag hroute
  have hleft : tag (route ew m) = ew := htag ew hew m hm
  have hright : tag (route ew' m') = ew' := htag ew' hew' m' hm'
  exact hne (by simpa [hleft, hright] using htag_eq)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
    {β : ℝ} {n : ℕ}
    (htagged :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases htagged v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, tag, hinj, htag, hpoint⟩
  refine ⟨ownerOf, howner, route, hinj, ?_, hpoint⟩
  intro ew hew ew' hew' hne m hm m' hm' hroute
  have htag_eq : tag (route ew m) = tag (route ew' m') :=
    congrArg tag hroute
  have hleft : tag (route ew m) = ew := htag ew hew m hm
  have hright : tag (route ew' m') = ew' := htag ew' hew' m' hm'
  exact hne (by simpa [hleft, hright] using htag_eq)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (htagged :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
      htagged.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
      htagged.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hownerRoute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  rcases hownerRoute v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, hinj, hcross, hpoint⟩
  refine ⟨fun m => route (ownerOf m) m, ?_, ?_⟩
  · exact
      finset_injOn_assembledRoute_of_ownerFiltered_injOn
        Ωactive (doubledBoxOriginIncidentEdges n) ownerOf route
        (fun m hm => (howner m hm).1) hinj hcross
  · intro m hm
    exact hpoint m hm

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hownerRoute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  rcases hownerRoute v hvwedge hlt hypos e0 hedge Ω with
    ⟨ownerOf, howner, route, hinj, hcross, hpoint⟩
  refine ⟨fun m => route (ownerOf m) m, ?_, ?_⟩
  · exact
      finset_injOn_assembledRoute_of_ownerFiltered_injOn
        Ωactive (doubledBoxOriginIncidentEdges n) ownerOf route
        (fun m hm => (howner m hm).1) hinj hcross
  · intro m hm
    exact hpoint m hm

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hownerRoute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
      hownerRoute.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
      hownerRoute.2⟩

end Exact3D
end StatMech
