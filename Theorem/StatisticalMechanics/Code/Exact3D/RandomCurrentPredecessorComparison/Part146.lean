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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part138
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_forall_supportPattern_routes
    {β : ℝ} {n : ℕ}
    (hcase :
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
                    ∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      ∃ emptyRoute : Profile → Profile,
                        ∃ innerRoute : Profile → Profile,
                          Set.InjOn emptyRoute
                              (Ω.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S)) ∧
                            Set.InjOn innerRoute
                              (Ω.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S)) ∧
                              (∀ m ∈ Ω.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S),
                                doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                  β n v w e0 m ≤
                                  edgeCopySourcePairSummand
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (doubledBoxOriginToInnerEndpointSource n v)
                                    (∅ : Finset
                                      (FK.boxVerts 3 (2 * n)))
                                    (emptyRoute m) / 64) ∧
                                (∀ m ∈ Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                    β n v w e0 m ≤
                                    edgeCopySourcePairSummand
                                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                      (doubledBoxOriginToInnerEndpointSource n w)
                                      (doubledBoxInnerPairSource n v w)
                                      (innerRoute m) / 64)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
      β n := by
  intro v hvwedge hlt hypos w e0 hedge Ω
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  have hcaseTotal :
      ∀ S : Finset Edge,
        ∃ emptyRoute : Profile → Profile,
          ∃ innerRoute : Profile → Profile,
            S ∈ supportPatterns →
              Set.InjOn emptyRoute
                  (Ω.filter
                    (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
                Set.InjOn innerRoute
                  (Ω.filter
                    (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
                  (∀ m ∈ Ω.filter
                      (fun m => doubledBoxOriginIncidentSupport n m = S),
                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                      β n v w e0 m ≤
                      edgeCopySourcePairSummand
                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n v)
                        (∅ : Finset (FK.boxVerts 3 (2 * n)))
                        (emptyRoute m) / 64) ∧
                    (∀ m ∈ Ω.filter
                        (fun m => doubledBoxOriginIncidentSupport n m = S),
                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                        β n v w e0 m ≤
                        edgeCopySourcePairSummand
                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w)
                          (innerRoute m) / 64) := by
    intro S
    by_cases hS : S ∈ supportPatterns
    · rcases hcase v hvwedge hlt hypos e0 hedge Ω S hS with
        ⟨emptyRoute, innerRoute, hinjEmpty, hinjInner, hpointEmpty,
          hpointInner⟩
      exact
        ⟨emptyRoute, innerRoute, fun _ =>
          ⟨hinjEmpty, hinjInner,
            by
              intro m hm
              simpa [w] using hpointEmpty m hm,
            by
              intro m hm
              simpa [w] using hpointInner m hm⟩⟩
    · exact ⟨id, id, fun hS' => False.elim (hS hS')⟩
  refine
    ⟨(fun S => Classical.choose (hcaseTotal S)),
      (fun S => Classical.choose (Classical.choose_spec (hcaseTotal S))),
      ?_, ?_, ?_, ?_⟩
  · intro S hS
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.1
  · intro S hS
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.2.1
  · intro S hS m hm
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.2.2.1 m hm
  · intro S hS m hm
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.2.2.2 m hm

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_forall_nonempty_supportPattern_filter_routes
    {β : ℝ} {n : ℕ}
    (hcase :
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
                    ∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      (Ω.filter
                        (fun m =>
                          doubledBoxOriginIncidentSupport n m = S)).Nonempty →
                        ∃ emptyRoute : Profile → Profile,
                          ∃ innerRoute : Profile → Profile,
                            Set.InjOn emptyRoute
                                (Ω.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S)) ∧
                              Set.InjOn innerRoute
                                (Ω.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S)) ∧
                                (∀ m ∈ Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m = S),
                                  doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                    β n v w e0 m ≤
                                    edgeCopySourcePairSummand
                                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                      (doubledBoxOriginToInnerEndpointSource n v)
                                      (∅ : Finset
                                        (FK.boxVerts 3 (2 * n)))
                                      (emptyRoute m) / 64) ∧
                                  (∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m = S),
                                    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n w)
                                        (doubledBoxInnerPairSource n v w)
                                        (innerRoute m) / 64)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
      β n := by
  intro v hvwedge hlt hypos w e0 hedge Ω
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  have hcaseTotal :
      ∀ S : Finset Edge,
        ∃ emptyRoute : Profile → Profile,
          ∃ innerRoute : Profile → Profile,
            S ∈ supportPatterns →
              Set.InjOn emptyRoute
                  (Ω.filter
                    (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
                Set.InjOn innerRoute
                  (Ω.filter
                    (fun m => doubledBoxOriginIncidentSupport n m = S)) ∧
                  (∀ m ∈ Ω.filter
                      (fun m => doubledBoxOriginIncidentSupport n m = S),
                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                      β n v w e0 m ≤
                      edgeCopySourcePairSummand
                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n v)
                        (∅ : Finset (FK.boxVerts 3 (2 * n)))
                        (emptyRoute m) / 64) ∧
                    (∀ m ∈ Ω.filter
                        (fun m => doubledBoxOriginIncidentSupport n m = S),
                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                        β n v w e0 m ≤
                        edgeCopySourcePairSummand
                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w)
                          (innerRoute m) / 64) := by
    intro S
    by_cases hS : S ∈ supportPatterns
    · by_cases hnonempty :
          (Ω.filter
            (fun m => doubledBoxOriginIncidentSupport n m = S)).Nonempty
      · rcases hcase v hvwedge hlt hypos e0 hedge Ω S hS hnonempty with
          ⟨emptyRoute, innerRoute, hinjEmpty, hinjInner, hpointEmpty,
            hpointInner⟩
        exact
          ⟨emptyRoute, innerRoute, fun _ =>
            ⟨hinjEmpty, hinjInner,
              by
                intro m hm
                simpa [w] using hpointEmpty m hm,
              by
                intro m hm
                simpa [w] using hpointInner m hm⟩⟩
      · exact
          ⟨id, id, fun _ =>
            ⟨Set.injOn_id _, Set.injOn_id _,
              by
                intro m hm
                exact False.elim (hnonempty ⟨m, hm⟩),
              by
                intro m hm
                exact False.elim (hnonempty ⟨m, hm⟩)⟩⟩
    · exact ⟨id, id, fun hS' => False.elim (hS hS')⟩
  refine
    ⟨(fun S => Classical.choose (hcaseTotal S)),
      (fun S => Classical.choose (Classical.choose_spec (hcaseTotal S))),
      ?_, ?_, ?_, ?_⟩
  · intro S hS
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.1
  · intro S hS
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.2.1
  · intro S hS m hm
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.2.2.1 m hm
  · intro S hS m hm
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec (hcaseTotal S))) hS
    exact hspec.2.2.2 m hm

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_singleton_and_multi_supportPattern_filter_routes
    {β : ℝ} {n : ℕ}
    (hsingle :
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
                    ∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      S.card = 1 →
                        (Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S)).Nonempty →
                          ∃ emptyRoute : Profile → Profile,
                            ∃ innerRoute : Profile → Profile,
                              Set.InjOn emptyRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                Set.InjOn innerRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                  (∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n v)
                                        (∅ : Finset
                                          (FK.boxVerts 3 (2 * n)))
                                        (emptyRoute m) / 64) ∧
                                    (∀ m ∈ Ω.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                        β n v w e0 m ≤
                                        edgeCopySourcePairSummand
                                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                          (doubledBoxOriginToInnerEndpointSource n w)
                                          (doubledBoxInnerPairSource n v w)
                                          (innerRoute m) / 64))
    (hmulti :
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
                    ∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      1 < S.card →
                        (Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S)).Nonempty →
                          ∃ emptyRoute : Profile → Profile,
                            ∃ innerRoute : Profile → Profile,
                              Set.InjOn emptyRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                Set.InjOn innerRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                  (∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n v)
                                        (∅ : Finset
                                          (FK.boxVerts 3 (2 * n)))
                                        (emptyRoute m) / 64) ∧
                                    (∀ m ∈ Ω.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                        β n v w e0 m ≤
                                        edgeCopySourcePairSummand
                                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                          (doubledBoxOriginToInnerEndpointSource n w)
                                          (doubledBoxInnerPairSource n v w)
                                          (innerRoute m) / 64)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_forall_nonempty_supportPattern_filter_routes
      ?_
  dsimp only at hsingle hmulti ⊢
  intro v hvwedge hlt hypos e0 hedge Ω S hS hnonempty
  classical
  by_cases hcard : S.card = 1
  · exact hsingle v hvwedge hlt hypos e0 hedge Ω S hS hcard hnonempty
  · have hS_nonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
    have hcard_pos : 0 < S.card := Finset.Nonempty.card_pos hS_nonempty
    have hcard_multi : 1 < S.card := by omega
    exact hmulti v hvwedge hlt hypos e0 hedge Ω S hS hcard_multi hnonempty

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_singleton_owner_filter_routes_and_multi_supportPattern_filter_routes
    {β : ℝ} {n : ℕ}
    (hsingleOwner :
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
                    ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                      (Ω.filter
                        (fun m =>
                          doubledBoxOriginIncidentSupport n m =
                            {ew})).Nonempty →
                        ∃ emptyRoute : Profile → Profile,
                          ∃ innerRoute : Profile → Profile,
                            Set.InjOn emptyRoute
                                (Ω.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew)) ∧
                              Set.InjOn innerRoute
                                (Ω.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew)) ∧
                                (∀ m ∈ Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                  doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                    β n v w e0 m ≤
                                    edgeCopySourcePairSummand
                                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                      (doubledBoxOriginToInnerEndpointSource n v)
                                      (∅ : Finset
                                        (FK.boxVerts 3 (2 * n)))
                                      (emptyRoute m) / 64) ∧
                                  (∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n w)
                                        (doubledBoxInnerPairSource n v w)
                                        (innerRoute m) / 64))
    (hmulti :
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
                    ∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      1 < S.card →
                        (Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S)).Nonempty →
                          ∃ emptyRoute : Profile → Profile,
                            ∃ innerRoute : Profile → Profile,
                              Set.InjOn emptyRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                Set.InjOn innerRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                  (∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n v)
                                        (∅ : Finset
                                          (FK.boxVerts 3 (2 * n)))
                                        (emptyRoute m) / 64) ∧
                                    (∀ m ∈ Ω.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                        β n v w e0 m ≤
                                        edgeCopySourcePairSummand
                                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                          (doubledBoxOriginToInnerEndpointSource n w)
                                          (doubledBoxInnerPairSource n v w)
                                          (innerRoute m) / 64)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_singleton_and_multi_supportPattern_filter_routes
      ?_ hmulti
  dsimp only at hsingleOwner ⊢
  intro v hvwedge hlt hypos e0 hedge Ω S hS hcard hnonempty
  classical
  rcases
      doubledBoxNonemptyOriginIncidentSupportPattern_eq_singleton_of_card_eq_one
        (n := n) (S := S) hS hcard with
    ⟨ew, hew, hS_eq⟩
  have hnonempty_singleton :
      (Ω.filter
        (fun m => doubledBoxOriginIncidentSupport n m = {ew})).Nonempty := by
    simpa [hS_eq] using hnonempty
  rcases hsingleOwner v hvwedge hlt hypos e0 hedge Ω ew hew
      hnonempty_singleton with
    ⟨emptyRoute, innerRoute, hinjEmptyOwner, hinjInnerOwner,
      hpointEmptyOwner, hpointInnerOwner⟩
  have hsubset :
      Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = {ew}) ⊆
        Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew) :=
    doubledBoxOriginIncidentSupport_singleton_filter_subset_originIncidentOwner_filter
      (n := n) Ω ew
  refine ⟨emptyRoute, innerRoute, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hroute
    exact hinjEmptyOwner
      (hsubset (by simpa [hS_eq] using ha))
      (hsubset (by simpa [hS_eq] using hb)) hroute
  · intro a ha b hb hroute
    exact hinjInnerOwner
      (hsubset (by simpa [hS_eq] using ha))
      (hsubset (by simpa [hS_eq] using hb)) hroute
  · intro m hm
    exact hpointEmptyOwner m (hsubset (by simpa [hS_eq] using hm))
  · intro m hm
    exact hpointInnerOwner m (hsubset (by simpa [hS_eq] using hm))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_singleton_multiplicity_filter_routes_and_multi_supportPattern_filter_routes
    {β : ℝ} {n : ℕ}
    (hsingleMultiplicity :
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
                    ∀ ew ∈ doubledBoxOriginIncidentEdges n,
                      (Ω.filter
                        (fun m =>
                          doubledBoxOriginIncidentSupport n m =
                            {ew})).Nonempty →
                        ∃ emptyRoute : Profile → Profile,
                          ∃ innerRoute : Profile → Profile,
                            Set.InjOn emptyRoute
                                (Ω.filter (fun m => m ew ≠ 0)) ∧
                              Set.InjOn innerRoute
                                  (Ω.filter (fun m => m ew ≠ 0)) ∧
                                (∀ m ∈ Ω.filter (fun m => m ew ≠ 0),
                                  doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                    β n v w e0 m ≤
                                    edgeCopySourcePairSummand
                                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                      (doubledBoxOriginToInnerEndpointSource n v)
                                      (∅ : Finset
                                        (FK.boxVerts 3 (2 * n)))
                                      (emptyRoute m) / 64) ∧
                                  (∀ m ∈ Ω.filter (fun m => m ew ≠ 0),
                                    doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n w)
                                        (doubledBoxInnerPairSource n v w)
                                        (innerRoute m) / 64))
    (hmulti :
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
                    ∀ S ∈
                        Finset.filter (fun S => S.Nonempty)
                          (Finset.powerset
                            (doubledBoxOriginIncidentEdges n)),
                      1 < S.card →
                        (Ω.filter
                          (fun m =>
                            doubledBoxOriginIncidentSupport n m = S)).Nonempty →
                          ∃ emptyRoute : Profile → Profile,
                            ∃ innerRoute : Profile → Profile,
                              Set.InjOn emptyRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                Set.InjOn innerRoute
                                  (Ω.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                        S)) ∧
                                  (∀ m ∈ Ω.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m =
                                          S),
                                    doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand
                                      β n v w e0 m ≤
                                      edgeCopySourcePairSummand
                                        (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                        (doubledBoxOriginToInnerEndpointSource n v)
                                        (∅ : Finset
                                          (FK.boxVerts 3 (2 * n)))
                                        (emptyRoute m) / 64) ∧
                                    (∀ m ∈ Ω.filter
                                        (fun m =>
                                          doubledBoxOriginIncidentSupport n m =
                                            S),
                                      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand
                                        β n v w e0 m ≤
                                        edgeCopySourcePairSummand
                                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                          (doubledBoxOriginToInnerEndpointSource n w)
                                          (doubledBoxInnerPairSource n v w)
                                          (innerRoute m) / 64)) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
      β n := by
  refine
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt_of_singleton_owner_filter_routes_and_multi_supportPattern_filter_routes
      ?_ hmulti
  dsimp only at hsingleMultiplicity ⊢
  intro v hvwedge hlt hypos e0 hedge Ω ew hew hnonempty
  rcases hsingleMultiplicity v hvwedge hlt hypos e0 hedge Ω ew hew
      hnonempty with
    ⟨emptyRoute, innerRoute, hinjEmptyMultiplicity, hinjInnerMultiplicity,
      hpointEmptyMultiplicity, hpointInnerMultiplicity⟩
  have hsubset :
      Ω.filter (fun m => doubledBoxOriginIncidentOwner n m = some ew) ⊆
        Ω.filter (fun m => m ew ≠ 0) :=
    doubledBoxOriginIncidentOwner_filter_subset_multiplicity_filter
      (n := n) Ω ew
  refine ⟨emptyRoute, innerRoute, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hroute
    exact hinjEmptyMultiplicity (hsubset ha) (hsubset hb) hroute
  · intro a ha b hb hroute
    exact hinjInnerMultiplicity (hsubset ha) (hsubset hb) hroute
  · intro m hm
    exact hpointEmptyMultiplicity m (hsubset hm)
  · intro m hm
    exact hpointInnerMultiplicity m (hsubset hm)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourSourcePairInjectionChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAt
      β n := by
  intro v hvwedge hlt hypos w e0 hedge Ω
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hcharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨emptyRoute, innerRoute, hinjEmpty, hinjInner, hpointEmpty,
      hpointInner⟩
  refine
    ⟨(fun S m =>
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) (emptyRoute S m) / 64),
      (fun S m =>
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) (innerRoute S m) / 64),
      ?_, ?_, ?_, ?_⟩
  · intro S hS m hm
    simpa [supportPatterns] using hpointEmpty S hS m hm
  · intro S hS m hm
    simpa [supportPatterns, w] using hpointInner S hS m hm
  · intro S hS
    let s : Finset Profile :=
      Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S)
    have hroute :
        (∑ m ∈ s,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))
            (emptyRoute S m)) ≤
          doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
      simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum, s] using
        edgeCopySourcePairSummand_finset_sum_route_le_sourcePairSum_of_injOn
          (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
          (by intro e; norm_num)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) s
          (emptyRoute S)
          (by
            simpa [supportPatterns, s] using hinjEmpty S hS)
    calc
      (∑ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) (emptyRoute S m) / 64)
          =
          (∑ m ∈ s,
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n)))
              (emptyRoute S m)) / 64 := by
        rw [Finset.sum_div]
      _ ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v / 64 :=
        div_le_div_of_nonneg_right hroute (by norm_num)
  · intro S hS
    let s : Finset Profile :=
      Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S)
    have hroute :
        (∑ m ∈ s,
          edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)
            (innerRoute S m)) ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
      simpa [s] using
        edgeCopySourcePairSummand_finset_sum_route_le_sourcePairSum_of_injOn
          (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
          (by intro e; norm_num)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) s
          (innerRoute S)
          (by
            simpa [supportPatterns, s] using hinjInner S hS)
    calc
      (∑ m ∈ Ω.filter
          (fun m => doubledBoxOriginIncidentSupport n m = S),
        edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) (innerRoute S m) / 64)
          =
          (∑ m ∈ s,
            edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)
              (innerRoute S m)) / 64 := by
        rw [Finset.sum_div]
      _ ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) / 64 :=
        div_le_div_of_nonneg_right hroute (by norm_num)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseSixtyFourBudgetBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAt
      β n := by
  intro v hvwedge hlt hypos w e0 hedge Ω
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨emptyBudget, innerBudget, hpointEmpty, hpointInner,
      hshareEmpty, hshareInner⟩
  refine
    ⟨emptyBudget, innerBudget, hpointEmpty, hpointInner, ?_, ?_⟩
  · have htarget :
        0 ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
      simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum,
        sourcePairSum_eq_edgeCopySourcePairSum] using
        edgeCopySourcePairSum_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) hβ
          (by intro e; norm_num)
    have hsum :=
      doubledBoxNonemptyOriginIncidentSupportPatterns_sum_le_of_forall_le_div_64
        (n := n)
        (F := fun S =>
          ∑ m ∈ Ω.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            emptyBudget S m)
        (target := doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v)
        htarget
        (by
          intro S hS
          simpa [supportPatterns] using hshareEmpty S hS)
    simpa [supportPatterns] using hsum
  · have htarget :
        0 ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
      simpa [sourcePairSum_eq_edgeCopySourcePairSum] using
        edgeCopySourcePairSum_nonneg (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) hβ
          (by intro e; norm_num)
    have hsum :=
      doubledBoxNonemptyOriginIncidentSupportPatterns_sum_le_of_forall_le_div_64
        (n := n)
        (F := fun S =>
          ∑ m ∈ Ω.filter
              (fun m => doubledBoxOriginIncidentSupport n m = S),
            innerBudget S m)
        (target :=
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w))
        htarget
        (by
          intro S hS
          simpa [supportPatterns, w] using hshareInner S hS)
    simpa [supportPatterns, w] using hsum

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAt
    {β : ℝ} {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternPointwiseBudgetBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  classical
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨emptyBudget, innerBudget, hpointEmpty, hpointInner, htotalEmpty,
      htotalInner⟩
  have htotalEmptyExplicit :
      (∑ S ∈ supportPatterns,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (fun m => m)
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (emptyBudget S)) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
    calc
      (∑ S ∈ supportPatterns,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (fun m => m)
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (emptyBudget S)) =
          ∑ S ∈ supportPatterns,
            ∑ m ∈ Ω.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              emptyBudget S m := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
        simpa [supportPatterns] using htotalEmpty
  have htotalInnerExplicit :
      (∑ S ∈ supportPatterns,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (fun m => m)
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (innerBudget S)) ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) := by
    calc
      (∑ S ∈ supportPatterns,
        finiteSupportExplicitCaseBudgetTotal
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (fun m => m)
          (Ω.filter (fun m => doubledBoxOriginIncidentSupport n m = S))
          (innerBudget S)) =
          ∑ S ∈ supportPatterns,
            ∑ m ∈ Ω.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              innerBudget S m := by
        refine Finset.sum_congr rfl ?_
        intro S hS
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
        simpa [supportPatterns, w] using htotalInner
  refine
    ⟨Profile,
      (fun S => Ω.filter
        (fun m => doubledBoxOriginIncidentSupport n m = S)),
      (fun _S m => m),
      emptyBudget, emptyBudget, innerBudget, innerBudget, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
  · intro S hS m hm
    exact hm
  · intro S hS m hm
    simpa [w] using hpointEmpty S (by simpa [supportPatterns] using hS) m hm
  · intro S hS m hm
    simpa [w] using hpointInner S (by simpa [supportPatterns] using hS) m hm
  · intro S hS c hc
    exact le_rfl
  · intro S hS c hc
    exact le_rfl
  · simpa [supportPatterns] using htotalEmptyExplicit
  · simpa [supportPatterns, w] using htotalInnerExplicit

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  classical
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m => doubledBoxOriginTouchesEdgeSupport n m
  let Ωactive :=
    Ω.filter active
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, supportCaseSet, supportCaseOf, supportEmptyRowBound,
      supportEmptyRelaxedBudget, supportInnerRowBound,
      supportInnerRelaxedBudget, hcoverSupport, hpointEmptySupport,
      hpointInnerSupport, hrelaxEmptySupport, hrelaxInnerSupport,
      htotalEmptySupport, htotalInnerSupport⟩
  let Fempty :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  let Finner :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → ℝ :=
    fun m =>
      doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
        (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m
  have hsumEmpty :
      Finset.sum Ωactive Fempty ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := by
    have hsum :
        (∑ m ∈ Ω.filter
            (fun m => doubledBoxOriginTouchesEdgeSupport n m),
          Fempty m) ≤
          doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
      finset_sum_le_of_doubledBoxOriginIncidentSupportPatternFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        (n := n) (κ := κ) Ω Fempty supportCaseOf supportCaseSet
        supportEmptyRowBound supportEmptyRelaxedBudget hcoverSupport
        hpointEmptySupport hrelaxEmptySupport htotalEmptySupport
    simpa [Ωactive, active] using hsum
  have hsumInner :
      Finset.sum Ωactive Finner ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := by
    have hsum :
        (∑ m ∈ Ω.filter
            (fun m => doubledBoxOriginTouchesEdgeSupport n m),
          Finner m) ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
      finset_sum_le_of_doubledBoxOriginIncidentSupportPatternFilters_finiteSupportExplicitCaseBudgetTotal_le_of_relaxed
        (n := n) (κ := κ) Ω Finner supportCaseOf supportCaseSet
        supportInnerRowBound supportInnerRelaxedBudget hcoverSupport
        hpointInnerSupport hrelaxInnerSupport htotalInnerSupport
    simpa [Ωactive, active] using hsum
  refine
    ⟨Ωactive, (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ), Ωactive,
      (fun m => m), Fempty, Fempty, Finner, Finner, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
  · simp [Ωactive]
  · intro m hm
    simp [Ωactive, active, hm]
  · intro m hm
    exact hm
  · intro m _hm
    exact le_rfl
  · intro m _hm
    exact le_rfl
  · intro c _hc
    exact le_rfl
  · intro c _hc
    exact le_rfl
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωactive (fun m => m) Ωactive
          Fempty =
        Finset.sum Ωactive Fempty :=
          finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum Ωactive
            Fempty
      _ ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
        hsumEmpty
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωactive (fun m => m) Ωactive
          Finner =
        Finset.sum Ωactive Finner :=
          finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum Ωactive
            Finner
      _ ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
        hsumInner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginIncidentSupportPatternRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAt_of_selectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffCommonOriginTouchingActiveRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCommonOriginTouchingPredicateActiveRelaxedExplicitCaseTableBoundsAt
      β n := by
  classical
  intro v hvwedge hlt hypos e0 hedge Ω
  let active :
      (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) → Prop :=
    fun m => doubledBoxOriginTouchesEdgeSupport n m
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨Ωactive, κ, caseSet, caseOf, emptyRowBound, emptyRelaxedBudget,
      innerRowBound, innerRelaxedBudget, hsubset, hactive_iff, hcover,
      hpointEmpty, hpointInner, hrelaxEmpty, hrelaxInner, htotalEmpty,
      htotalInner⟩
  have hΩactive_eq : Ωactive = Ω.filter active := by
    ext m
    constructor
    · intro hm
      exact Finset.mem_filter.mpr
        ⟨hsubset hm, (hactive_iff m (hsubset hm)).1 hm⟩
    · intro hm
      rcases Finset.mem_filter.mp hm with ⟨hmΩ, hactive⟩
      exact (hactive_iff m hmΩ).2 hactive
  let hactive : DecidablePred active := Classical.decPred active
  refine ⟨hactive, ?_⟩
  letI : DecidablePred active := hactive
  refine
    ⟨κ, caseSet, caseOf, (fun c => β * emptyRowBound c),
      (fun c => β * emptyRelaxedBudget c),
      (fun c => β * innerRowBound c),
      (fun c => β * innerRelaxedBudget c), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact hcover m (by simpa [hΩactive_eq] using hm)
  · intro m hm
    have hsel :
        doubledBoxSelectedCopyTotalPairCardEmptySourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          emptyRowBound (caseOf m) :=
      hpointEmpty m (by simpa [hΩactive_eq] using hm)
    rw [
      doubledBoxSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_totalPairCardEmptySourcePairSummand]
    exact mul_le_mul_of_nonneg_left hsel hβ
  · intro m hm
    have hsel :
        doubledBoxSelectedCopyTotalPairCardInnerPairSourcePairSummand β n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0 m ≤
          innerRowBound (caseOf m) :=
      hpointInner m (by simpa [hΩactive_eq] using hm)
    rw [
      doubledBoxSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_totalPairCardInnerPairSourcePairSummand]
    exact mul_le_mul_of_nonneg_left hsel hβ
  · intro c hc
    exact mul_le_mul_of_nonneg_left (hrelaxEmpty c hc) hβ
  · intro c hc
    exact mul_le_mul_of_nonneg_left (hrelaxInner c hc) hβ
  · constructor
    · calc
        finiteSupportExplicitCaseBudgetTotal (Ω.filter active) caseOf caseSet
            (fun c => β * emptyRelaxedBudget c)
            = β *
                finiteSupportExplicitCaseBudgetTotal (Ω.filter active) caseOf
                  caseSet emptyRelaxedBudget := by
              rw [finiteSupportExplicitCaseBudgetTotal_const_mul]
        _ = β *
                finiteSupportExplicitCaseBudgetTotal Ωactive caseOf caseSet
                  emptyRelaxedBudget := by
              rw [← hΩactive_eq]
        _ ≤ β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
              mul_le_mul_of_nonneg_left htotalEmpty hβ
    · calc
        finiteSupportExplicitCaseBudgetTotal (Ω.filter active) caseOf caseSet
            (fun c => β * innerRelaxedBudget c)
            = β *
                finiteSupportExplicitCaseBudgetTotal (Ω.filter active) caseOf
                  caseSet innerRelaxedBudget := by
              rw [finiteSupportExplicitCaseBudgetTotal_const_mul]
        _ = β *
                finiteSupportExplicitCaseBudgetTotal Ωactive caseOf caseSet
                  innerRelaxedBudget := by
              rw [← hΩactive_eq]
        _ ≤
            β *
              Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                (doubledBoxOriginToInnerEndpointSource n
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
                (doubledBoxInnerPairSource n v
                  (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
              mul_le_mul_of_nonneg_left htotalInner hβ

end Exact3D
end StatMech
