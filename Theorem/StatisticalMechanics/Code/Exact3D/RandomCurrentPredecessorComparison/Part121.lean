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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part113
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt_of_forall_emptySourceEquationCellRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hcell :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only at hcell ⊢
  intro e0 hedge Ω S hS ew hew
  simpa [ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsAt] using
    hcell v hvwedge hlt hypos e0 hedge Ω S hS ew hew

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt_of_forall_innerPairSourceEquationCellRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hcell :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only at hcell ⊢
  intro e0 hedge Ω S hS ew hew
  simpa [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsAt] using
    hcell v hvwedge hlt hypos e0 hedge Ω S hS ew hew

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt_of_forall_empty_innerSourceEquationCellRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hempty :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew)
    (hinner :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew) :
    ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only at hempty hinner ⊢
  intro e0 hedge Ω
  exact
    ⟨(exactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt_of_forall_emptySourceEquationCellRouteShareBoundsAt
        hempty) v hvwedge hlt hypos e0 hedge Ω,
      (exactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt_of_forall_innerPairSourceEquationCellRouteShareBoundsAt
        hinner) v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt
        β n)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt
        β n) :
    ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only at hempty hinner ⊢
  intro e0 hedge Ω
  exact
    ⟨hempty v hvwedge hlt hypos e0 hedge Ω,
      hinner v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt_of_sourceEquationRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hsource :
      ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt
        β n) :
    ExactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hsource ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hsource v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptySource, hinnerSource⟩
  constructor
  · intro S hS ew hew
    rcases hemptySource S (by simpa [supportPatterns] using hS) ew hew with
      ⟨profileRoute, witness, hinj, hleft, hright, hpoint⟩
    refine ⟨profileRoute, witness, hinj, ?_, hpoint⟩
    intro m
    exact
      (edgeCopySourcePairWitnesses_mem (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) (profileRoute m)
        (witness m)).mpr
        ⟨hleft m, hright m⟩
  · intro S hS ew hew
    rcases hinnerSource S (by simpa [supportPatterns] using hS) ew hew with
      ⟨profileRoute, witness, hinj, hleft, hright, hpoint⟩
    refine ⟨profileRoute, witness, hinj, ?_, hpoint⟩
    intro m
    exact
      (edgeCopySourcePairWitnesses_mem (FK.boxGraph 3 (2 * n))
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) (profileRoute m) (witness m)).mpr
        ⟨hleft m, hright m⟩

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt
        β n)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt
        β n) :
    ExactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt
      β n :=
  exactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt_of_sourceEquationRouteShareBoundsAt
    (exactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
      hempty hinner)

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hempty :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationRouteShareBoundsAt
        β n)
    (hinner :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationRouteShareBoundsAt
        β n) :
    ExactSupportOwnerResidualSourcePairRouteShareBoundsAt β n :=
  exactSupportOwnerResidualSourcePairRouteShareBoundsAt_of_profileWitnessRouteShareBoundsAt
    (exactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt_of_empty_innerSourceEquationRouteShareBoundsAt
      hempty hinner)

set_option linter.style.longLine false in


theorem
    filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt_of_exactSupportOwnerResidualSourcePairRouteShareBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hroutes : ExactSupportOwnerResidualSourcePairRouteShareBoundsAt β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hroutes ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hroutes v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyRoutes, hinnerRoutes⟩
  constructor
  · intro S hS ew hew
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    rcases hemptyRoutes S (by simpa [supportPatterns] using hS) ew hew with
      ⟨route, hinj, hpoint⟩
    have hpointSum :
        (∑ m ∈ cell,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
            β n v w e0 m) ≤
          ∑ m ∈ cell,
            ((β / 6) *
              edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (route m)) /
              384 := by
      exact
        Finset.sum_le_sum
          (fun m hm => hpoint m (by simpa [cell, Ωactive, w] using hm))
    have hroute :
        (∑ m ∈ cell,
          (β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route m)) ≤
          (β / 6) *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
      exact
        edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_le_sourcePairSum_of_injOn
          (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
          (by intro e; norm_num)
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) cell route
          (by simpa [cell, Ωactive, w] using hinj)
    change
      (∑ m ∈ cell,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m) ≤
        ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
          6) /
          384
    calc
      (∑ m ∈ cell,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
          β n v w e0 m) ≤
          ∑ m ∈ cell,
            ((β / 6) *
              edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (route m)) /
              384 := hpointSum
      _ =
          (∑ m ∈ cell,
            (β / 6) *
              edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (route m)) /
            384 := by
        rw [Finset.sum_div]
      _ ≤
          ((β / 6) *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n)))) /
            384 :=
        div_le_div_of_nonneg_right hroute (by norm_num)
      _ =
          ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
            6) /
            384 := by
        simp [doubledBoxOriginToInnerEndpointSourcePairEmptySum]
        ring
  · intro S hS ew hew
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    rcases hinnerRoutes S (by simpa [supportPatterns] using hS) ew hew with
      ⟨route, hinj, hpoint⟩
    have hpointSum :
        (∑ m ∈ cell,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v w e0 m) ≤
          ∑ m ∈ cell,
            ((β / 6) *
              edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (route m)) /
              384 := by
      exact
        Finset.sum_le_sum
          (fun m hm => hpoint m (by simpa [cell, Ωactive, w] using hm))
    have hroute :
        (∑ m ∈ cell,
          (β / 6) *
            edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (route m)) ≤
          (β / 6) *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w) := by
      exact
        edgeCopySourcePairDataWeight_finset_sum_route_beta_div_six_le_sourcePairSum_of_injOn
          (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
          (by intro e; norm_num)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) cell route
          (by simpa [cell, Ωactive, w] using hinj)
    change
      (∑ m ∈ cell,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m) ≤
        ((β *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6) /
          384
    calc
      (∑ m ∈ cell,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
          β n v w e0 m) ≤
          ∑ m ∈ cell,
            ((β / 6) *
              edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (route m)) /
              384 := hpointSum
      _ =
          (∑ m ∈ cell,
            (β / 6) *
              edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β
                (fun _ => 1) (route m)) /
            384 := by
        rw [Finset.sum_div]
      _ ≤
          ((β / 6) *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            384 :=
        div_le_div_of_nonneg_right hroute (by norm_num)
      _ =
          ((β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
          6) /
            384 := by
        ring

set_option maxHeartbeats 500000 in

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
        β n v w e0 m) ≤
      ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
        384 := by
  classical
  dsimp only
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  let Fempty : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt]
    at hcell
  rcases hcell with
    ⟨profileRoute, witness, hinjProfile, hleft, hright, hpoint⟩
  have hwitness :
      ∀ a : {m : Profile // m ∈ cell},
        witness a ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) (profileRoute a) := by
    intro a
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a, hright a⟩
  let route :
      {m : Profile // m ∈ cell} →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
    fun a => edgeCopySourcePairData_of_witness G (hwitness a)
  have hinjData : Function.Injective route := by
    intro a b hroute
    exact hinjProfile (by
      simpa [route] using congrArg Sigma.fst hroute)
  have hpointSum :
      (∑ m ∈ cell, Fempty m) ≤
        ∑ a ∈ cell.attach,
          ((β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route a)) /
            384 := by
    calc
      (∑ m ∈ cell, Fempty m) =
          ∑ a ∈ cell.attach, Fempty a.1 := by
        exact (Finset.sum_attach cell Fempty).symm
      _ ≤
          ∑ a ∈ cell.attach,
            ((β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route a)) /
              384 := by
        refine Finset.sum_le_sum ?_
        intro a _ha
        simpa [Fempty, route, G] using hpoint a.1 a.2
  have hroute :
      (∑ a ∈ cell.attach,
        (β / 6) *
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
            (route a)) ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    exact
      edgeCopySourcePairDataWeight_finset_attach_sum_route_beta_div_six_le_sourcePairSum_of_injective
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) cell route hinjData
  change
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
        β n v w e0 m) ≤
      ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
        384
  calc
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
        β n v w e0 m) =
        ∑ m ∈ cell, Fempty m := rfl
    _ ≤
        ∑ a ∈ cell.attach,
          ((β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route a)) /
            384 := hpointSum
    _ =
        (∑ a ∈ cell.attach,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route a)) /
          384 := by
      rw [Finset.sum_div]
    _ ≤
        ((β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))) /
          384 :=
      div_le_div_of_nonneg_right hroute (by norm_num)
    _ =
        ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
          384 := by
      simp [doubledBoxOriginToInnerEndpointSourcePairEmptySum, G]
      ring

set_option maxHeartbeats 500000 in

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
        β n v w e0 m) ≤
      ((β *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6) /
        384 := by
  classical
  dsimp only
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  let Finner : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt]
    at hcell
  rcases hcell with
    ⟨profileRoute, witness, hinjProfile, hleft, hright, hpoint⟩
  have hwitness :
      ∀ a : {m : Profile // m ∈ cell},
        witness a ∈
          edgeCopySourcePairWitnesses G
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) (profileRoute a) := by
    intro a
    rw [edgeCopySourcePairWitnesses_mem]
    exact ⟨hleft a, hright a⟩
  let route :
      {m : Profile // m ∈ cell} →
        edgeCopySourcePairData G
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
    fun a => edgeCopySourcePairData_of_witness G (hwitness a)
  have hinjData : Function.Injective route := by
    intro a b hroute
    exact hinjProfile (by
      simpa [route] using congrArg Sigma.fst hroute)
  have hpointSum :
      (∑ m ∈ cell, Finner m) ≤
        ∑ a ∈ cell.attach,
          ((β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route a)) /
            384 := by
    calc
      (∑ m ∈ cell, Finner m) =
          ∑ a ∈ cell.attach, Finner a.1 := by
        exact (Finset.sum_attach cell Finner).symm
      _ ≤
          ∑ a ∈ cell.attach,
            ((β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route a)) /
              384 := by
        refine Finset.sum_le_sum ?_
        intro a _ha
        simpa [Finner, route, G] using hpoint a.1 a.2
  have hroute :
      (∑ a ∈ cell.attach,
        (β / 6) *
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
            (route a)) ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
    exact
      edgeCopySourcePairDataWeight_finset_attach_sum_route_beta_div_six_le_sourcePairSum_of_injective
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) cell route hinjData
  change
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
        β n v w e0 m) ≤
      ((β *
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6) /
        384
  calc
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
        β n v w e0 m) =
        ∑ m ∈ cell, Finner m := rfl
    _ ≤
        ∑ a ∈ cell.attach,
          ((β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route a)) /
            384 := hpointSum
    _ =
        (∑ a ∈ cell.attach,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route a)) /
          384 := by
      rw [Finset.sum_div]
    _ ≤
        ((β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          384 :=
      div_le_div_of_nonneg_right hroute (by norm_num)
    _ =
        ((β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6) /
          384 := by
      ring

set_option maxHeartbeats 300000 in

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
        β n v w e0 m) ≤
      ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
        384 := by
  classical
  dsimp only
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  let Fempty : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt]
    at hcell
  rcases hcell with ⟨Split, split, route, hinj, hpoint⟩
  have hshare :
      (∑ m ∈ cell, Fempty m) ≤
        ((β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))) /
          6) /
          384 := by
    exact
      finset_sum_le_sourcePairShare_of_splitDataRoute_beta_div_six_div_384_pointwise
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) cell Fempty split route hinj
        (by
          intro a
          simpa [Fempty, G] using hpoint a.1 a.2)
  change
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
        β n v w e0 m) ≤
      ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
        384
  simpa [Fempty, doubledBoxOriginToInnerEndpointSourcePairEmptySum, G] using
    hshare

set_option maxHeartbeats 300000 in

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
        β n v w e0 m) ≤
      ((β *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6) /
        384 := by
  classical
  dsimp only
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  let Finner : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt]
    at hcell
  rcases hcell with ⟨Split, split, route, hinj, hpoint⟩
  have hshare :
      (∑ m ∈ cell, Finner m) ≤
        ((β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6) /
          384 := by
    exact
      finset_sum_le_sourcePairShare_of_splitDataRoute_beta_div_six_div_384_pointwise
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) cell Finner split route hinj
        (by
          intro a
          simpa [Finner, G] using hpoint a.1 a.2)
  change
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
        β n v w e0 m) ≤
      ((β *
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6) /
        384
  simpa [Finner, G] using hshare

set_option maxHeartbeats 300000 in

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt_sum_le_sourcePairShare
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
        β n v w e0 ew m) ≤
      ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
        384 := by
  classical
  dsimp only
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  let Fempty : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
        β n v w e0 ew m
  dsimp only
    [ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt]
    at hcell
  rcases hcell with ⟨Split, split, route, hinj, hpoint⟩
  have hshare :
      (∑ m ∈ cell, Fempty m) ≤
        ((β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n)))) /
          6) /
          384 := by
    exact
      finset_sum_le_sourcePairShare_of_splitDataRoute_beta_div_six_div_384_pointwise
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) cell Fempty split route hinj
        (by
          intro a
          simpa [Fempty, G] using hpoint a.1 a.2)
  change
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
        β n v w e0 ew m) ≤
      ((β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6) /
        384
  simpa [Fempty, doubledBoxOriginToInnerEndpointSourcePairEmptySum, G] using
    hshare

set_option maxHeartbeats 300000 in

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt_sum_le_sourcePairShare
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {v : FK.boxVerts 3 n}
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    {e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ)}
    {S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    {ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset}
    (hcell :
      ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt
        β n v hvwedge hlt hypos e0 Ω S ew) :
    let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
    let Profile := Edge → ℕ
    let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
    let Ωactive : Finset Profile :=
      Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m) ≤
      ((β *
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6) /
        384 := by
  classical
  dsimp only
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let cell : Finset Profile :=
    Ωactive.filter
      (fun m =>
        doubledBoxOriginIncidentSupport n m = S ∧
          doubledBoxOriginIncidentOwner n m = some ew)
  let Finner : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m
  dsimp only
    [ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt]
    at hcell
  rcases hcell with ⟨Split, split, route, hinj, hpoint⟩
  have hshare :
      (∑ m ∈ cell, Finner m) ≤
        ((β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6) /
          384 := by
    exact
      finset_sum_le_sourcePairShare_of_splitDataRoute_beta_div_six_div_384_pointwise
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) cell Finner split route hinj
        (by
          intro a
          simpa [Finner, G] using hpoint a.1 a.2)
  change
    (∑ m ∈ cell,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
        β n v w e0 ew m) ≤
      ((β *
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6) /
        384
  simpa [Finner, G] using hshare

set_option maxHeartbeats 200000 in


set_option linter.style.longLine false in


theorem
    filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSplitDataFiniteCellRouteShareBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hempty :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew)
    (hinner :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hempty hinner ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  constructor
  · intro S hS ew hew
    simpa [Ωactive, supportPatterns, w] using
      exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hempty v hvwedge hlt hypos e0 hedge Ω S
          (by simpa [supportPatterns] using hS) ew hew)
  · intro S hS ew hew
    simpa [Ωactive, supportPatterns, w] using
      exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hinner v hvwedge hlt hypos e0 hedge Ω S
          (by simpa [supportPatterns] using hS) ew hew)

set_option maxHeartbeats 200000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSplitDataFiniteCellRouteShareAtEdgeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hempty :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ew ≠ e0 →
                          ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt
                            β n v hvwedge hlt hypos e0 Ω S ew)
    (hinner :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ew ≠ e0 →
                          ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt
                            β n v hvwedge hlt hypos e0 Ω S ew) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hempty hinner ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  constructor
  · intro S hS ew hew hmis
    simpa [Ωactive, supportPatterns, w] using
      exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt_sum_le_sourcePairShare
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hempty v hvwedge hlt hypos e0 hedge Ω S
          (by simpa [supportPatterns] using hS) ew hew hmis)
  · intro S hS ew hew hmis
    simpa [Ωactive, supportPatterns, w] using
      exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt_sum_le_sourcePairShare
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hinner v hvwedge hlt hypos e0 hedge Ω S
          (by simpa [supportPatterns] using hS) ew hew hmis)

set_option maxHeartbeats 200000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hempty :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ew ≠ e0 →
                          ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt
                            β n v hvwedge hlt hypos e0 Ω S ew)
    (hinner :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ew ≠ e0 →
                          ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
                            β n v hvwedge hlt hypos e0 Ω S ew) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSplitDataFiniteCellRouteShareAtEdgeBoundsAt
    hβ
    (fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis =>
      exactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_sourceEquationFiniteCellRouteShareAtEdgeBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hempty v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis))
    (fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis =>
      exactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt_of_sourceEquationFiniteCellRouteShareAtEdgeBoundsAt
        (β := β) (n := n) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hinner v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis))

set_option maxHeartbeats 200000 in


set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSingletonSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hempty :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ew ≠ e0 →
                          ∃ m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                            ∃ profile0 :
                                ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                              ∃ witness0 :
                                  Finset
                                    (Sharpness.FluxEdgeCopy.Copy
                                      (FK.boxGraph 3 (2 * n)) profile0),
                                (let Edge :=
                                    ↥(FK.boxGraph 3 (2 * n)).edgeFinset
                                  let Profile := Edge → ℕ
                                  let w :=
                                    boxVertStrictSectorYPredecessor3 v
                                      hvwedge hlt hypos
                                  let Ωactive : Finset Profile :=
                                    Ω.filter
                                      (doubledBoxIncrementedFullSourceActive n
                                        w e0)
                                  Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m = S ∧
                                          doubledBoxOriginIncidentOwner n m =
                                            some ew) = {m0}) ∧
                                  Sharpness.RandomCurrent.sources
                                      (Sharpness.FluxEdgeCopy.endsM
                                        (FK.boxGraph 3 (2 * n)) profile0)
                                      witness0 =
                                    doubledBoxOriginToInnerEndpointSource n v ∧
                                    Sharpness.RandomCurrent.sources
                                        (Sharpness.FluxEdgeCopy.endsM
                                          (FK.boxGraph 3 (2 * n)) profile0)
                                        ((Finset.univ :
                                            Finset
                                              (Sharpness.FluxEdgeCopy.Copy
                                                (FK.boxGraph 3 (2 * n))
                                                profile0)) \
                                          witness0) =
                                      (∅ :
                                        Finset (FK.boxVerts 3 (2 * n))) ∧
                                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                                          β n v
                                          (boxVertStrictSectorYPredecessor3 v
                                            hvwedge hlt hypos)
                                          e0 ew m0 ≤
                                        ((β / 6) *
                                          Sharpness.weight
                                            (FK.boxGraph 3 (2 * n)) β
                                            (fun _ => 1)
                                            (Sharpness.ofEdgeFun
                                              (FK.boxGraph 3 (2 * n))
                                              profile0)) /
                                          384)
    (hinner :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ew ≠ e0 →
                          ∃ m0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                            ∃ profile0 :
                                ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ,
                              ∃ witness0 :
                                  Finset
                                    (Sharpness.FluxEdgeCopy.Copy
                                      (FK.boxGraph 3 (2 * n)) profile0),
                                (let Edge :=
                                    ↥(FK.boxGraph 3 (2 * n)).edgeFinset
                                  let Profile := Edge → ℕ
                                  let w :=
                                    boxVertStrictSectorYPredecessor3 v
                                      hvwedge hlt hypos
                                  let Ωactive : Finset Profile :=
                                    Ω.filter
                                      (doubledBoxIncrementedFullSourceActive n
                                        w e0)
                                  Ωactive.filter
                                      (fun m =>
                                        doubledBoxOriginIncidentSupport n m = S ∧
                                          doubledBoxOriginIncidentOwner n m =
                                            some ew) = {m0}) ∧
                                  Sharpness.RandomCurrent.sources
                                      (Sharpness.FluxEdgeCopy.endsM
                                        (FK.boxGraph 3 (2 * n)) profile0)
                                      witness0 =
                                    doubledBoxOriginToInnerEndpointSource n
                                      (boxVertStrictSectorYPredecessor3 v
                                        hvwedge hlt hypos) ∧
                                    Sharpness.RandomCurrent.sources
                                        (Sharpness.FluxEdgeCopy.endsM
                                          (FK.boxGraph 3 (2 * n)) profile0)
                                        ((Finset.univ :
                                            Finset
                                              (Sharpness.FluxEdgeCopy.Copy
                                                (FK.boxGraph 3 (2 * n))
                                                profile0)) \
                                          witness0) =
                                      doubledBoxInnerPairSource n v
                                        (boxVertStrictSectorYPredecessor3 v
                                          hvwedge hlt hypos) ∧
                                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                                          β n v
                                          (boxVertStrictSectorYPredecessor3 v
                                            hvwedge hlt hypos)
                                          e0 ew m0 ≤
                                        ((β / 6) *
                                          Sharpness.weight
                                            (FK.boxGraph 3 (2 * n)) β
                                            (fun _ => 1)
                                            (Sharpness.ofEdgeFun
                                              (FK.boxGraph 3 (2 * n))
                                              profile0)) /
                                          384) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternStrictMismatchOwnerPairShareAtEdgeResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    hβ
    (fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis => by
      rcases hempty v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis with
        ⟨m0, profile0, witness0, hcell, hleft, hright, hpoint⟩
      exact
        exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_singleton
          (β := β) (n := n) hvwedge hlt hypos
          (e0 := e0) (Ω := Ω) (S := S) (ew := ew) (m0 := m0)
          hcell profile0 witness0 hleft hright hpoint)
    (fun v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis => by
      rcases hinner v hvwedge hlt hypos e0 hedge Ω S hS ew hew hmis with
        ⟨m0, profile0, witness0, hcell, hleft, hright, hpoint⟩
      exact
        exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt_of_cell_eq_singleton
          (β := β) (n := n) hvwedge hlt hypos
          (e0 := e0) (Ω := Ω) (S := S) (ew := ew) (m0 := m0)
          hcell profile0 witness0 hleft hright hpoint)


set_option maxHeartbeats 200000 in

set_option linter.style.longLine false in


theorem
    filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt_of_forall_empty_innerSourceEquationFiniteCellRouteShareBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hempty :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew)
    (hinner :
      ∀ v : FK.boxVerts 3 n,
        (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v) →
          (hlt :
            ((v : Lattice.Site 3) (1 : Fin 3)) <
              ((v : Lattice.Site 3) (2 : Fin 3))) →
            (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3))) →
              let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
              ∀ e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset,
                e0.1 =
                    s(FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) v,
                      FK.boxVertInclLE 3 (by omega : n ≤ 2 * n) w) →
                  ∀ Ω :
                      Finset
                        (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ),
                    let supportPatterns :
                        Finset
                          (Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset) :=
                      Finset.filter (fun S => S.Nonempty)
                        (Finset.powerset (doubledBoxOriginIncidentEdges n))
                    ∀ S ∈ supportPatterns,
                      ∀ ew ∈ S,
                        ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
                          β n v hvwedge hlt hypos e0 Ω S ew) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerPairShareResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hempty hinner ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  constructor
  · intro S hS ew hew
    simpa [Ωactive, supportPatterns, w] using
      exactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hempty v hvwedge hlt hypos e0 hedge Ω S
          (by simpa [supportPatterns] using hS) ew hew)
  · intro S hS ew hew
    simpa [Ωactive, supportPatterns, w] using
      exactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt_sum_le_sourcePairShare
        (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
        (e0 := e0) (Ω := Ω) (S := S) (ew := ew)
        (hinner v hvwedge hlt hypos e0 hedge Ω S
          (by simpa [supportPatterns] using hS) ew hew)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt_of_filterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternUpdateSelectedEdgeMultiplicityResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
      β n := by
  classical
  intro v hvwedge hlt hypos
  dsimp only at hbounds ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  let Fempty : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  let Finner : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v w
        e0 m
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyTotal, hinnerTotal⟩
  have htouch :
      Ωtouch = Ωactive := by
    simpa [Ωtouch, Ωactive, w] using
      doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
  constructor
  · calc
      ∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
            e0 m =
          ∑ m ∈ Ωtouch, Fempty m := by
        simpa [Fempty] using
          congrArg (fun T : Finset Profile => ∑ m ∈ T, Fempty m)
            htouch.symm
      _ =
          ∑ S ∈ supportPatterns,
            ∑ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              Fempty m := by
        simpa [Ωtouch, Ωactive, supportPatterns, Fempty, w] using
          doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
            (n := n) Ωactive Fempty
      _ ≤
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                Fempty m := by
        simpa [Ωactive, supportPatterns, Fempty, w] using
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
            (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
            (e0 := e0) hedge Ω
      _ ≤
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
            6 := by
        simpa [Ωactive, supportPatterns, Fempty, w] using hemptyTotal
  · calc
      ∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
            w e0 m =
          ∑ m ∈ Ωtouch, Finner m := by
        simpa [Finner] using
          congrArg (fun T : Finset Profile => ∑ m ∈ T, Finner m)
            htouch.symm
      _ =
          ∑ S ∈ supportPatterns,
            ∑ m ∈ Ωactive.filter
                (fun m => doubledBoxOriginIncidentSupport n m = S),
              Finner m := by
        simpa [Ωtouch, Ωactive, supportPatterns, Finner, w] using
          doubledBoxOriginTouchesEdgeSupport_filter_sum_eq_sum_nonempty_originIncidentSupportPatternFilters
            (n := n) Ωactive Finner
      _ ≤
          ∑ S ∈ supportPatterns,
            ∑ ew ∈ S,
              ∑ m ∈ Ωactive.filter
                  (fun m =>
                    (Function.update m e0 (m e0 + 1)) ew ≠ 0),
                Finner m := by
        simpa [Ωactive, supportPatterns, Finner, w] using
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_activeOriginIncidentSupportPatterns_sum_le_updateSelectedEdgeMultiplicityBudget_sum_of_strictSectorYPredecessor3
            (β := β) hβ (n := n) (v := v) hvwedge hlt hypos
            (e0 := e0) hedge Ω
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6 := by
        simpa [Ωactive, supportPatterns, Finner, w] using hinnerTotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsAt_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωtouch : Finset Profile :=
    (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
      (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hempty, hinner⟩
  constructor
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωtouch (fun m => m) Ωtouch
          (fun m =>
            β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m) =
          ∑ m ∈ Ωtouch,
            (β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
                  β n v w e0 m) := by
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ =
          ∑ m ∈ Ωtouch,
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
              β n v w e0 m := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [
          ←
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand_eq_beta_mul_inCurrent_add_beta_mul_outsideCurrent]
      _ ≤
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) /
            6 := by
        simpa [Ωtouch, w] using hempty
  · calc
      finiteSupportExplicitCaseBudgetTotal Ωtouch (fun m => m) Ωtouch
          (fun m =>
            β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m) =
          ∑ m ∈ Ωtouch,
            (β *
                doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m +
              β *
                doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
                  β n v w e0 m) := by
        rw [finiteSupportExplicitCaseBudgetTotal_self_eq_finset_sum]
      _ =
          ∑ m ∈ Ωtouch,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [
          ←
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand_eq_beta_mul_inCurrent_add_beta_mul_outsideCurrent]
      _ ≤
          (β *
            Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
              (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w)) /
            6 := by
        simpa [Ωtouch, w] using hinner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt_of_filterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthCanonicalFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportBranchwiseInOutSelectedCopySixthNonnegativeRelaxedExplicitCaseTableFiniteBudgetAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωtouch : Finset Profile :=
    (Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)).filter
      (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  rcases hbounds v hvwedge hlt hypos e0 hedge Ω with
    ⟨hempty, hinner⟩
  refine
    ⟨Profile, (fun _ => Ωtouch), (fun _ m => m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m),
      (fun _ m =>
        β *
          doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand
            β n v w e0 m),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ew _hew m hm
    exact hm
  · intro ew _hew m hm
    rfl
  · intro ew _hew m hm
    rfl
  · intro ew _hew m hm
    rfl
  · intro ew _hew m hm
    rfl
  · intro ew _hew c hc
    rfl
  · intro ew _hew c hc
    rfl
  · intro ew _hew c hc
    rfl
  · intro ew _hew c hc
    rfl
  · intro ew _hew c hc
    exact
      add_nonneg
        (mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardEmptySourcePairSummand_nonneg
            (β := β) hβ (n := n) (v := v) (w := w) e0 c))
        (mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardEmptySourcePairSummand_nonneg
            (β := β) hβ (n := n) (v := v) (w := w) e0 c))
  · intro ew _hew c hc
    exact
      add_nonneg
        (mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyInCurrentPairCardInnerPairSourcePairSummand_nonneg
            (β := β) hβ (n := n) (v := v) (w := w) e0 c))
        (mul_nonneg hβ
          (doubledBoxSwitchedSelectedCopyOutsideCurrentPairCardInnerPairSourcePairSummand_nonneg
            (β := β) hβ (n := n) (v := v) (w := w) e0 c))
  · intro ew _hew
    simpa [Ωtouch, w] using hempty
  · intro ew _hew
    simpa [Ωtouch, w] using hinner

end Exact3D
end StatMech
