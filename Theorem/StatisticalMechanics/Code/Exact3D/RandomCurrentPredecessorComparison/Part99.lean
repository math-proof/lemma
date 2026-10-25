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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part91
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_multiplicitySupport_routes
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
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew))) ∧
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
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                  profileRoute ew m ew ≠ 0) ∧
                                (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                    ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                      e ≠ ew → profileRoute ew m e = 0) ∧
                                  ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                    ∀ m ∈ Ωactive.filter
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
                                              (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
      β n := by
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hleft, hright, hpos, hzero, hpoint⟩
  refine ⟨profileRoute, witness, hinj, hleft, hright, ?_, hpoint⟩
  intro ew hew m hm
  exact
    doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
      (n := n) (m := profileRoute ew m) (ew := ew) hew
      (hpos ew hew m hm) (hzero ew hew m hm)

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_multiplicitySupport_routes
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
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew))) ∧
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
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                  profileRoute ew m ew ≠ 0) ∧
                                (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                    ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                      e ≠ ew → profileRoute ew m e = 0) ∧
                                  ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                    ∀ m ∈ Ωactive.filter
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
                                              (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
      β n := by
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hleft, hright, hpos, hzero, hpoint⟩
  refine ⟨profileRoute, witness, hinj, hleft, hright, ?_, hpoint⟩
  intro ew hew m hm
  exact
    doubledBoxOriginIncidentSupport_eq_singleton_of_mem_of_ne_zero_of_forall_ne_eq_zero
      (n := n) (m := profileRoute ew m) (ew := ew) hew
      (hpos ew hew m hm) (hzero ew hew m hm)

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundsAt_of_forall_originIncidentOwner_sourceEquation_multiplicitySupport_routes
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
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew))) ∧
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
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                  profileRoute ew m ew ≠ 0) ∧
                                (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                    ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                      e ≠ ew → profileRoute ew m e = 0) ∧
                                  ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                    ∀ m ∈ Ωactive.filter
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
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew))) ∧
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
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                  profileRoute ew m ew ≠ 0) ∧
                                (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                  ∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                    ∀ e ∈ doubledBoxOriginIncidentEdges n,
                                      e ≠ ew → profileRoute ew m e = 0) ∧
                                  ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                                    ∀ m ∈ Ωactive.filter
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
                                              (profileRoute ew m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_multiplicitySupport_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_multiplicitySupport_routes
      hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_ownerSupportSingletonPointwiseSourceEquationRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_routes
    hroute

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_ownerSupportSingletonPointwiseSourceEquationRouteBoundAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_routes
    hroute

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_ownerSupportSingletonPointwiseSourceEquationRouteBoundsAt
    {β : ℝ} {n : ℕ}
    (hroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonPointwiseSourceEquationRouteBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_ownerSupportSingletonPointwiseSourceEquationRouteBoundAt
      hroute.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_ownerSupportSingletonPointwiseSourceEquationRouteBoundAt
      hroute.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_updateSelectedEdgeMultiplicity_filter_routes
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
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter
                            (fun m =>
                              (Function.update m e0 (m e0 + 1)) ew ≠
                                0))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                (Function.update m e0 (m e0 + 1)) ew ≠
                                  0),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  (Function.update m e0 (m e0 + 1)) ew ≠
                                    0),
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinjMultiplicity, hsupportMultiplicity, hpointMultiplicity⟩
  refine ⟨route, ?_, ?_, ?_⟩
  · intro ew hew a ha b hb hab
    have hsubset :
        Ωactive.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
          Ωactive.filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (by simpa [w] using hedge) Ω
    exact hinjMultiplicity ew hew (hsubset ha) (hsubset hb) hab
  · intro ew hew m hm
    have hsubset :
        Ωactive.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
          Ωactive.filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (by simpa [w] using hedge) Ω
    exact hsupportMultiplicity ew hew m (hsubset hm)
  · intro ew hew m hm
    have hsubset :
        Ωactive.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
          Ωactive.filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (by simpa [w] using hedge) Ω
    exact hpointMultiplicity ew hew m (hsubset hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_updateSelectedEdgeMultiplicity_filter_routes
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
                              (Function.update m e0 (m e0 + 1)) ew ≠
                                0))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                (Function.update m e0 (m e0 + 1)) ew ≠
                                  0),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  (Function.update m e0 (m e0 + 1)) ew ≠
                                    0),
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinjMultiplicity, hsupportMultiplicity, hpointMultiplicity⟩
  refine ⟨route, ?_, ?_, ?_⟩
  · intro ew hew a ha b hb hab
    have hsubset :
        Ωactive.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
          Ωactive.filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (by simpa [w] using hedge) Ω
    exact hinjMultiplicity ew hew (hsubset ha) (hsubset hb) hab
  · intro ew hew m hm
    have hsubset :
        Ωactive.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
          Ωactive.filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (by simpa [w] using hedge) Ω
    exact hsupportMultiplicity ew hew m (hsubset hm)
  · intro ew hew m hm
    have hsubset :
        Ωactive.filter
            (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
          Ωactive.filter
            (fun m => (Function.update m e0 (m e0 + 1)) ew ≠ 0) := by
      simpa [Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_originIncidentOwner_filter_subset_updateSelectedEdge_multiplicity_filter_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (ew := ew)
          (by simpa [w] using hedge) Ω
    exact hpointMultiplicity ew hew m (hsubset hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_forall_updateSelectedEdgeMultiplicity_filter_routes
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
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter
                            (fun m =>
                              (Function.update m e0 (m e0 + 1)) ew ≠
                                0))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                (Function.update m e0 (m e0 + 1)) ew ≠
                                  0),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  (Function.update m e0 (m e0 + 1)) ew ≠
                                    0),
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m))
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
                              (Function.update m e0 (m e0 + 1)) ew ≠
                                0))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                (Function.update m e0 (m e0 + 1)) ew ≠
                                  0),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  (Function.update m e0 (m e0 + 1)) ew ≠
                                    0),
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_updateSelectedEdgeMultiplicity_filter_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_updateSelectedEdgeMultiplicity_filter_routes
      hinner⟩

end Exact3D
end StatMech
