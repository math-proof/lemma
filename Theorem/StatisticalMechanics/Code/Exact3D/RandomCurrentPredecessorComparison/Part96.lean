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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part88
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ route : Finset Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ S ∈ supportPatterns,
                        Set.InjOn (route S)
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S))) ∧
                        (∀ S ∈ supportPatterns,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            doubledBoxOriginIncidentSupport n
                              (route S m).1 = S) ∧
                          ∀ S ∈ supportPatterns,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route S m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hroute ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hsupport, hpoint⟩
  have howner_mem :
      ∀ m ∈ Ωactive, doubledBoxOriginIncidentSupport n m ∈
        supportPatterns := by
    intro m hm
    rw [Finset.mem_filter]
    refine
      ⟨doubledBoxOriginIncidentSupport_mem_originIncidentEdges_powerset,
        ?_⟩
    have hactive :
        doubledBoxIncrementedFullSourceActive n w e0 m := by
      exact (Finset.mem_filter.mp (by simpa [Ωactive] using hm)).2
    have htouch :
        doubledBoxOriginTouchesEdgeSupport n m := by
      simpa [w] using
        doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
          (m := m) (by simpa [w] using hedge) hactive
    exact
      (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
        (n := n) (m := m)).2 htouch
  refine
    ⟨fun m => route (doubledBoxOriginIncidentSupport n m) m, ?_, ?_⟩
  · exact
      finset_injOn_assembledRoute_of_ownerFiltered_injOn_tag
        Ωactive supportPatterns (doubledBoxOriginIncidentSupport n) route
        (fun d => doubledBoxOriginIncidentSupport n d.1)
        howner_mem hinj
        (by
          intro S hS m hm
          exact hsupport S hS m hm)
  · intro m hm
    exact hpoint (doubledBoxOriginIncidentSupport n m)
      (howner_mem m hm) m (Finset.mem_filter.mpr ⟨hm, rfl⟩)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ route : Finset Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ S ∈ supportPatterns,
                        Set.InjOn (route S)
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S))) ∧
                        (∀ S ∈ supportPatterns,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            doubledBoxOriginIncidentSupport n
                              (route S m).1 = S) ∧
                          ∀ S ∈ supportPatterns,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route S m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hroute ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hsupport, hpoint⟩
  have howner_mem :
      ∀ m ∈ Ωactive, doubledBoxOriginIncidentSupport n m ∈
        supportPatterns := by
    intro m hm
    rw [Finset.mem_filter]
    refine
      ⟨doubledBoxOriginIncidentSupport_mem_originIncidentEdges_powerset,
        ?_⟩
    have hactive :
        doubledBoxIncrementedFullSourceActive n w e0 m := by
      exact (Finset.mem_filter.mp (by simpa [Ωactive] using hm)).2
    have htouch :
        doubledBoxOriginTouchesEdgeSupport n m := by
      simpa [w] using
        doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0)
          (m := m) (by simpa [w] using hedge) hactive
    exact
      (doubledBoxOriginIncidentSupport_nonempty_iff_originTouchesEdgeSupport
        (n := n) (m := m)).2 htouch
  refine
    ⟨fun m => route (doubledBoxOriginIncidentSupport n m) m, ?_, ?_⟩
  · exact
      finset_injOn_assembledRoute_of_ownerFiltered_injOn_tag
        Ωactive supportPatterns (doubledBoxOriginIncidentSupport n) route
        (fun d => doubledBoxOriginIncidentSupport n d.1)
        howner_mem hinj
        (by
          intro S hS m hm
          exact hsupport S hS m hm)
  · intro m hm
    exact hpoint (doubledBoxOriginIncidentSupport n m)
      (howner_mem m hm) m (Finset.mem_filter.mpr ⟨hm, rfl⟩)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt_of_forall_originIncidentSupportPattern_data_routes
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ route : Finset Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ S ∈ supportPatterns,
                        Set.InjOn (route S)
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S))) ∧
                        (∀ S ∈ supportPatterns,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            doubledBoxOriginIncidentSupport n
                              (route S m).1 = S) ∧
                          ∀ S ∈ supportPatterns,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route S m))
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ route : Finset Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ S ∈ supportPatterns,
                        Set.InjOn (route S)
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentSupport n m = S))) ∧
                        (∀ S ∈ supportPatterns,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S),
                            doubledBoxOriginIncidentSupport n
                              (route S m).1 = S) ∧
                          ∀ S ∈ supportPatterns,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S),
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route S m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
      hinner⟩

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_profileWitness_routes
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ profileRoute : Finset Edge → Profile → Profile,
                      ∃ witness :
                          (S : Finset Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute S m)),
                        (∀ S ∈ supportPatterns,
                          Set.InjOn (profileRoute S)
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S))) ∧
                          (∀ S m,
                            witness S m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))
                                (profileRoute S m)) ∧
                            (∀ S ∈ supportPatterns,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute S m) = S) ∧
                              ∀ S ∈ supportPatterns,
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute S m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
  simpa [F, Ωactive, supportPatterns, w] using
    edgeCopySourcePairData_supportPattern_routes_of_profileWitness_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive supportPatterns (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hwitness hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_profileWitness_routes
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ profileRoute : Finset Edge → Profile → Profile,
                      ∃ witness :
                          (S : Finset Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute S m)),
                        (∀ S ∈ supportPatterns,
                          Set.InjOn (profileRoute S)
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S))) ∧
                          (∀ S m,
                            witness S m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n w)
                                (doubledBoxInnerPairSource n v w)
                                (profileRoute S m)) ∧
                            (∀ S ∈ supportPatterns,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute S m) = S) ∧
                              ∀ S ∈ supportPatterns,
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute S m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
  simpa [F, Ωactive, supportPatterns, w] using
    edgeCopySourcePairData_supportPattern_routes_of_profileWitness_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive supportPatterns (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hwitness hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt_of_forall_originIncidentSupportPattern_profileWitness_routes
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ profileRoute : Finset Edge → Profile → Profile,
                      ∃ witness :
                          (S : Finset Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute S m)),
                        (∀ S ∈ supportPatterns,
                          Set.InjOn (profileRoute S)
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S))) ∧
                          (∀ S m,
                            witness S m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))
                                (profileRoute S m)) ∧
                            (∀ S ∈ supportPatterns,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute S m) = S) ∧
                              ∀ S ∈ supportPatterns,
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute S m)))
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ profileRoute : Finset Edge → Profile → Profile,
                      ∃ witness :
                          (S : Finset Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute S m)),
                        (∀ S ∈ supportPatterns,
                          Set.InjOn (profileRoute S)
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S))) ∧
                          (∀ S m,
                            witness S m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n w)
                                (doubledBoxInnerPairSource n v w)
                                (profileRoute S m)) ∧
                            (∀ S ∈ supportPatterns,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute S m) = S) ∧
                              ∀ S ∈ supportPatterns,
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute S m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_profileWitness_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_profileWitness_routes
      hinner⟩

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_profileWitness_singleton_multi_checks
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ profileRoute : Finset Edge → Profile → Profile,
                      ∃ witness :
                          (S : Finset Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute S m)),
                        (∀ S m,
                          witness S m ∈
                            edgeCopySourcePairWitnesses
                              (FK.boxGraph 3 (2 * n))
                              (doubledBoxOriginToInnerEndpointSource n v)
                              (∅ : Finset (FK.boxVerts 3 (2 * n)))
                              (profileRoute S m)) ∧
                          (∀ S ∈ supportPatterns,
                            S.card = 1 →
                              Set.InjOn (profileRoute S)
                                  (Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                (∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S),
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute S m) = S) ∧
                                  ∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                      β n v w e0 m ≤
                                      (β / 6) *
                                        Sharpness.weight
                                          (FK.boxGraph 3 (2 * n)) β
                                          (fun _ => 1)
                                          (Sharpness.ofEdgeFun
                                            (FK.boxGraph 3 (2 * n))
                                            (profileRoute S m))) ∧
                            ∀ S ∈ supportPatterns,
                              1 < S.card →
                                Set.InjOn (profileRoute S)
                                    (Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S)) ∧
                                  (∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxOriginIncidentSupport n
                                      (profileRoute S m) = S) ∧
                                    ∀ m ∈ Ωactive.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                        β n v w e0 m ≤
                                        (β / 6) *
                                          Sharpness.weight
                                            (FK.boxGraph 3 (2 * n)) β
                                            (fun _ => 1)
                                            (Sharpness.ofEdgeFun
                                              (FK.boxGraph 3 (2 * n))
                                              (profileRoute S m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hwitness, hsingle, hmulti⟩
  simpa [F, Ωactive, w] using
    edgeCopySourcePairData_doubledBoxOriginIncidentSupportPattern_routes_of_profileWitness_singleton_multi_checks
      (β := β) (c := β / 6) (n := n)
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      Ωactive F profileRoute witness hwitness hsingle hmulti

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_profileWitness_singleton_multi_checks
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
                    let supportPatterns : Finset (Finset Edge) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∃ profileRoute : Finset Edge → Profile → Profile,
                      ∃ witness :
                          (S : Finset Edge) → (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute S m)),
                        (∀ S m,
                          witness S m ∈
                            edgeCopySourcePairWitnesses
                              (FK.boxGraph 3 (2 * n))
                              (doubledBoxOriginToInnerEndpointSource n w)
                              (doubledBoxInnerPairSource n v w)
                              (profileRoute S m)) ∧
                          (∀ S ∈ supportPatterns,
                            S.card = 1 →
                              Set.InjOn (profileRoute S)
                                  (Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                (∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S),
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute S m) = S) ∧
                                  ∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                      β n v w e0 m ≤
                                      (β / 6) *
                                        Sharpness.weight
                                          (FK.boxGraph 3 (2 * n)) β
                                          (fun _ => 1)
                                          (Sharpness.ofEdgeFun
                                            (FK.boxGraph 3 (2 * n))
                                            (profileRoute S m))) ∧
                            ∀ S ∈ supportPatterns,
                              1 < S.card →
                                Set.InjOn (profileRoute S)
                                    (Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S)) ∧
                                  (∀ m ∈ Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxOriginIncidentSupport n
                                      (profileRoute S m) = S) ∧
                                    ∀ m ∈ Ωactive.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                        β n v w e0 m ≤
                                        (β / 6) *
                                          Sharpness.weight
                                            (FK.boxGraph 3 (2 * n)) β
                                            (fun _ => 1)
                                            (Sharpness.ofEdgeFun
                                              (FK.boxGraph 3 (2 * n))
                                              (profileRoute S m))) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_forall_originIncidentSupportPattern_data_routes
      ?_
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hwitness, hsingle, hmulti⟩
  simpa [F, Ωactive, w] using
    edgeCopySourcePairData_doubledBoxOriginIncidentSupportPattern_routes_of_profileWitness_singleton_multi_checks
      (β := β) (c := β / 6) (n := n)
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      Ωactive F profileRoute witness hwitness hsingle hmulti

end Exact3D
end StatMech
