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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part90
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
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
                              doubledBoxOriginIncidentOwner n m =
                                some ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
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
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinjOwner, hsupportOwner, hpointOwner⟩
  let ownerOf : Profile → Edge :=
    fun m =>
      match doubledBoxOriginIncidentOwner n m with
      | some ew => ew
      | none => e0
  have hownerActive :
      ∀ m ∈ Ωactive,
        ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
          doubledBoxOriginIncidentOwner n m = some (ownerOf m) := by
    intro m hm
    have hactive :
        doubledBoxIncrementedFullSourceActive n w e0 m :=
      (Finset.mem_filter.mp hm).2
    have htouch : doubledBoxOriginTouchesEdgeSupport n m := by
      exact
        doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          (by simpa [w] using hedge) (by simpa [w] using hactive)
    rcases doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
        (n := n) (m := m) htouch with
      ⟨ew, hew, howner, _hmew⟩
    have hownerOf : ownerOf m = ew := by
      simp [ownerOf, howner]
    exact ⟨by simpa [hownerOf] using hew, by simpa [hownerOf] using howner⟩
  refine ⟨ownerOf, hownerActive, route, ?_, ?_, ?_⟩
  · intro ew hew a ha b hb hab
    have ha_active : a ∈ Ωactive := (Finset.mem_filter.mp ha).1
    have hb_active : b ∈ Ωactive := (Finset.mem_filter.mp hb).1
    have ha_owner :
        doubledBoxOriginIncidentOwner n a = some ew := by
      have hcanonical := (hownerActive a ha_active).2
      simpa [(Finset.mem_filter.mp ha).2] using hcanonical
    have hb_owner :
        doubledBoxOriginIncidentOwner n b = some ew := by
      have hcanonical := (hownerActive b hb_active).2
      simpa [(Finset.mem_filter.mp hb).2] using hcanonical
    exact hinjOwner ew hew
      (by exact Finset.mem_filter.mpr ⟨ha_active, ha_owner⟩)
      (by exact Finset.mem_filter.mpr ⟨hb_active, hb_owner⟩) hab
  · intro ew hew m hm
    have hm_active : m ∈ Ωactive := (Finset.mem_filter.mp hm).1
    have hm_owner :
        doubledBoxOriginIncidentOwner n m = some ew := by
      have hcanonical := (hownerActive m hm_active).2
      simpa [(Finset.mem_filter.mp hm).2] using hcanonical
    exact hsupportOwner ew hew m
      (Finset.mem_filter.mpr ⟨hm_active, hm_owner⟩)
  · intro m hm
    exact hpointOwner (ownerOf m) (hownerActive m hm).1 m
      (Finset.mem_filter.mpr ⟨hm, (hownerActive m hm).2⟩)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
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
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentOwner n m =
                                some ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
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
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinjOwner, hsupportOwner, hpointOwner⟩
  let ownerOf : Profile → Edge :=
    fun m =>
      match doubledBoxOriginIncidentOwner n m with
      | some ew => ew
      | none => e0
  have hownerActive :
      ∀ m ∈ Ωactive,
        ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
          doubledBoxOriginIncidentOwner n m = some (ownerOf m) := by
    intro m hm
    have hactive :
        doubledBoxIncrementedFullSourceActive n w e0 m :=
      (Finset.mem_filter.mp hm).2
    have htouch : doubledBoxOriginTouchesEdgeSupport n m := by
      exact
        doubledBoxIncrementedFullSourceActive_originTouchesEdgeSupport_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) (m := m)
          (by simpa [w] using hedge) (by simpa [w] using hactive)
    rcases doubledBoxOriginIncidentOwner_exists_of_originTouchesEdgeSupport
        (n := n) (m := m) htouch with
      ⟨ew, hew, howner, _hmew⟩
    have hownerOf : ownerOf m = ew := by
      simp [ownerOf, howner]
    exact ⟨by simpa [hownerOf] using hew, by simpa [hownerOf] using howner⟩
  refine ⟨ownerOf, hownerActive, route, ?_, ?_, ?_⟩
  · intro ew hew a ha b hb hab
    have ha_active : a ∈ Ωactive := (Finset.mem_filter.mp ha).1
    have hb_active : b ∈ Ωactive := (Finset.mem_filter.mp hb).1
    have ha_owner :
        doubledBoxOriginIncidentOwner n a = some ew := by
      have hcanonical := (hownerActive a ha_active).2
      simpa [(Finset.mem_filter.mp ha).2] using hcanonical
    have hb_owner :
        doubledBoxOriginIncidentOwner n b = some ew := by
      have hcanonical := (hownerActive b hb_active).2
      simpa [(Finset.mem_filter.mp hb).2] using hcanonical
    exact hinjOwner ew hew
      (by exact Finset.mem_filter.mpr ⟨ha_active, ha_owner⟩)
      (by exact Finset.mem_filter.mpr ⟨hb_active, hb_owner⟩) hab
  · intro ew hew m hm
    have hm_active : m ∈ Ωactive := (Finset.mem_filter.mp hm).1
    have hm_owner :
        doubledBoxOriginIncidentOwner n m = some ew := by
      have hcanonical := (hownerActive m hm_active).2
      simpa [(Finset.mem_filter.mp hm).2] using hcanonical
    exact hsupportOwner ew hew m
      (Finset.mem_filter.mpr ⟨hm_active, hm_owner⟩)
  · intro m hm
    exact hpointOwner (ownerOf m) (hownerActive m hm).1 m
      (Finset.mem_filter.mpr ⟨hm, (hownerActive m hm).2⟩)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_forall_originIncidentOwner_filter_routes
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
                              doubledBoxOriginIncidentOwner n m =
                                some ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
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
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter
                            (fun m =>
                              doubledBoxOriginIncidentOwner n m =
                                some ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentOwner n m =
                                  some ew),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew),
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ew m)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      hinner⟩

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_profileWitness_routes
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
                            witness ew m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))
                                (profileRoute ew m)) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute ew m) = {ew}) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      ?_
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let rowPred : Edge → Profile → Prop :=
    fun ew m => doubledBoxOriginIncidentOwner n m = some ew
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, rowPred, w] using
    edgeCopySourcePairData_ownerIndexed_routes_of_profileWitness_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners rowPred (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hwitness hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_profileWitness_routes
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
                            witness ew m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n w)
                                (doubledBoxInnerPairSource n v w)
                                (profileRoute ew m)) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute ew m) = {ew}) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      ?_
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let rowPred : Edge → Profile → Prop :=
    fun ew m => doubledBoxOriginIncidentOwner n m = some ew
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hwitness, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, rowPred, w] using
    edgeCopySourcePairData_ownerIndexed_routes_of_profileWitness_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners rowPred (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hwitness hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_forall_originIncidentOwner_profileWitness_routes
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
                            witness ew m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n v)
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))
                                (profileRoute ew m)) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute ew m) = {ew}) ∧
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
                            witness ew m ∈
                              edgeCopySourcePairWitnesses
                                (FK.boxGraph 3 (2 * n))
                                (doubledBoxOriginToInnerEndpointSource n w)
                                (doubledBoxInnerPairSource n v w)
                                (profileRoute ew m)) ∧
                            (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew),
                                doubledBoxOriginIncidentSupport n
                                  (profileRoute ew m) = {ew}) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_profileWitness_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_profileWitness_routes
      hinner⟩

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_routes
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
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute ew m) = {ew}) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      ?_
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let rowPred : Edge → Profile → Prop :=
    fun ew m => doubledBoxOriginIncidentOwner n m = some ew
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hleft, hright, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, rowPred, w] using
    edgeCopySourcePairData_ownerIndexed_routes_of_sourceEquation_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners rowPred (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hleft hright hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_routes
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
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute ew m) = {ew}) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_filter_routes
      ?_
  classical
  dsimp only at hroute ⊢
  intro v hvwedge hlt hypos e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let owners : Finset Edge := doubledBoxOriginIncidentEdges n
  let rowPred : Edge → Profile → Prop :=
    fun ew m => doubledBoxOriginIncidentOwner n m = some ew
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hinj, hleft, hright, hsupport, hpoint⟩
  simpa [F, Ωactive, owners, rowPred, w] using
    edgeCopySourcePairData_ownerIndexed_routes_of_sourceEquation_routes
      (G := FK.boxGraph 3 (2 * n))
      (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w)
      (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
      Ωactive owners rowPred (doubledBoxOriginIncidentSupport n) F
      profileRoute witness hleft hright hinj hsupport hpoint

set_option maxHeartbeats 800000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt_of_forall_originIncidentOwner_sourceEquation_routes
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
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute ew m) = {ew}) ∧
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
                                  doubledBoxOriginIncidentSupport n
                                    (profileRoute ew m) = {ew}) ∧
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
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_routes
      hempty,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt_of_forall_originIncidentOwner_sourceEquation_routes
      hinner⟩

end Exact3D
end StatMech
