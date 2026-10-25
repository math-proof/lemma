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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part97
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt_of_activeSetSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hcase ⊢
  intro e0 hedge Ω hnonempty
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  have hrows :
      ∀ m : Profile,
        ∀ hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hm)).2
  exact hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt_of_activeSetSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hcase ⊢
  intro e0 hedge Ω hnonempty
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  have hrows :
      ∀ m : Profile,
        ∀ hm : m ∈ Ωactive,
          doubledBoxIncrementedFullSourceActive n w e0 m := by
    intro m hm
    exact (Finset.mem_filter.mp (by simpa [Ωactive] using hm)).2
  exact hcase v hvwedge hlt hypos e0 hedge Ωactive hrows hnonempty

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundsAt_of_activeSetSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt_of_activeSetSubrouteChargeBoundAt
      hcase.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt_of_activeSetSubrouteChargeBoundAt
      hcase.2⟩

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt_of_nonemptyActiveSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hcase ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  by_cases hnonempty : Ωactive.Nonempty
  · exact hcase v hvwedge hlt hypos e0 hedge Ω hnonempty
  · have hempty : Ωactive = ∅ := by
      ext m
      constructor
      · intro hm
        exact False.elim (hnonempty ⟨m, hm⟩)
      · intro hm
        simp at hm
    let F : Profile → ℝ :=
      fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
          e0 m
    exact
      edgeCopySourcePair_sourceEquationSubroute_of_empty
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n v)
        (B := (∅ : Finset (FK.boxVerts 3 (2 * n))))
        (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
        Ωactive F hempty

set_option maxHeartbeats 800000 in

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt_of_nonemptyActiveSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hcase ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  by_cases hnonempty : Ωactive.Nonempty
  · exact hcase v hvwedge hlt hypos e0 hedge Ω hnonempty
  · have hempty : Ωactive = ∅ := by
      ext m
      constructor
      · intro hm
        exact False.elim (hnonempty ⟨m, hm⟩)
      · intro hm
        simp at hm
    let F : Profile → ℝ :=
      fun m =>
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
          w e0 m
    exact
      edgeCopySourcePair_sourceEquationSubroute_of_empty
        (G := FK.boxGraph 3 (2 * n))
        (A := doubledBoxOriginToInnerEndpointSource n w)
        (B := doubledBoxInnerPairSource n v w)
        (β := β) (J := fun _ => (1 : ℝ)) (c := β / 6)
        Ωactive F hempty

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt_of_nonemptyActiveSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hcase :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt_of_nonemptyActiveSubrouteChargeBoundAt
      hcase.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt_of_nonemptyActiveSubrouteChargeBoundAt
      hcase.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases hsourceEq v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  refine ⟨profileRoute, witness, ?_, hinj, hpoint⟩
  intro m
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft m, hright m⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  rcases hsourceEq v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hleft, hright, hinj, hpoint⟩
  refine ⟨profileRoute, witness, ?_, hinj, hpoint⟩
  intro m
  rw [edgeCopySourcePairWitnesses_mem]
  exact ⟨hleft m, hright m⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
      hsourceEq.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
      hsourceEq.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hprofileWitness :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hprofileWitness v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hwitness, hinj, hpoint⟩
  exact
    edgeCopySourcePairData_attach_routes_of_profileWitness_routes
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n v)
      (B := (∅ : Finset (FK.boxVerts 3 (2 * n)))) β
      (fun _ => (1 : ℝ)) (β / 6) Ωactive F profileRoute witness
      hwitness hinj (fun m => hpoint m.1 m.2)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
    {β : ℝ} {n : ℕ}
    (hprofileWitness :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hprofileWitness v hvwedge hlt hypos e0 hedge Ω with
    ⟨profileRoute, witness, hwitness, hinj, hpoint⟩
  exact
    edgeCopySourcePairData_attach_routes_of_profileWitness_routes
      (G := G) (A := doubledBoxOriginToInnerEndpointSource n w)
      (B := doubledBoxInnerPairSource n v w) β (fun _ => (1 : ℝ))
      (β / 6) Ωactive F profileRoute witness hwitness hinj
      (fun m => hpoint m.1 m.2)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hprofileWitness :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
      hprofileWitness.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
      hprofileWitness.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt_of_nonemptyActiveSubrouteChargeBoundsAt
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundsAt_of_activeSetSubrouteChargeBoundsAt
        hsourceEq))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
    {β : ℝ} {n : ℕ}
    (hsourceEq :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt
      (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt_of_nonemptyActiveSubrouteChargeBoundsAt
        (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationNonemptyActiveSubrouteChargeBoundsAt_of_activeSetSubrouteChargeBoundsAt
          hsourceEq)))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hsubroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hsubroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  have hpoint_sum :
      (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) := by
    calc
      (∑ m ∈ Ωactive, F m) =
          ∑ x ∈ Ωactive.attach, F x.1 := by
        exact (Finset.sum_attach Ωactive F).symm
      _ ≤
          ∑ x ∈ Ωactive.attach,
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route x) := by
        refine Finset.sum_le_sum ?_
        intro x _hx
        exact hpoint x.1 x.2
  have hroute :
      (∑ x ∈ Ωactive.attach,
        (β / 6) *
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x)) ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    exact
      edgeCopySourcePairDataWeight_finset_attach_sum_route_beta_div_six_le_sourcePairSum_of_injective
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωactive route hinj
  change
    (∑ m ∈ Ωactive, F m) ≤
      (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6
  calc
    (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) :=
      hpoint_sum
    _ ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) := hroute
    _ =
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 := by
      simp [doubledBoxOriginToInnerEndpointSourcePairEmptySum]
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hsubroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hsubroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  have hpoint_sum :
      (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) := by
    calc
      (∑ m ∈ Ωactive, F m) =
          ∑ x ∈ Ωactive.attach, F x.1 := by
        exact (Finset.sum_attach Ωactive F).symm
      _ ≤
          ∑ x ∈ Ωactive.attach,
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route x) := by
        refine Finset.sum_le_sum ?_
        intro x _hx
        exact hpoint x.1 x.2
  have hroute :
      (∑ x ∈ Ωactive.attach,
        (β / 6) *
          edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x)) ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
    exact
      edgeCopySourcePairDataWeight_finset_attach_sum_route_beta_div_six_le_sourcePairSum_of_injective
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) Ωactive route hinj
  change
    (∑ m ∈ Ωactive, F m) ≤
      (β *
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6
  calc
    (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ)) (route x) :=
      hpoint_sum
    _ ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := hroute
    _ =
        (β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6 := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hsubroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact
    ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt
        hβ hsubroute.1 v hvwedge hlt hypos e0 hedge Ω,
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt
        hβ hsubroute.2 v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hsubroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m
  rcases hsubroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨Split, split, route, hinj, hpoint⟩
  have hpoint_sum :
      (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          ∑ i ∈ split x,
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route x i) := by
    calc
      (∑ m ∈ Ωactive, F m) =
          ∑ x ∈ Ωactive.attach, F x.1 := by
        exact (Finset.sum_attach Ωactive F).symm
      _ ≤
          ∑ x ∈ Ωactive.attach,
            ∑ i ∈ split x,
              (β / 6) *
                edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                  (route x i) := by
        refine Finset.sum_le_sum ?_
        intro x _hx
        exact hpoint x.1 x.2
  have hroute :
      (∑ x ∈ Ωactive.attach,
        ∑ i ∈ split x,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route x i)) ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) := by
    exact
      edgeCopySourcePairDataWeight_finset_attach_splitSum_route_beta_div_six_le_sourcePairSum_of_injOn
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωactive split route hinj
  change
    (∑ m ∈ Ωactive, F m) ≤
      (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6
  calc
    (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          ∑ i ∈ split x,
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route x i) := hpoint_sum
    _ ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n v)
            (∅ : Finset (FK.boxVerts 3 (2 * n))) := hroute
    _ =
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 := by
      simp [doubledBoxOriginToInnerEndpointSourcePairEmptySum]
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hsubroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let G := FK.boxGraph 3 (2 * n)
  let Edge := ↥G.edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let F : Profile → ℝ :=
    fun m =>
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m
  rcases hsubroute v hvwedge hlt hypos e0 hedge Ω with
    ⟨Split, split, route, hinj, hpoint⟩
  have hpoint_sum :
      (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          ∑ i ∈ split x,
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route x i) := by
    calc
      (∑ m ∈ Ωactive, F m) =
          ∑ x ∈ Ωactive.attach, F x.1 := by
        exact (Finset.sum_attach Ωactive F).symm
      _ ≤
          ∑ x ∈ Ωactive.attach,
            ∑ i ∈ split x,
              (β / 6) *
                edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                  (route x i) := by
        refine Finset.sum_le_sum ?_
        intro x _hx
        exact hpoint x.1 x.2
  have hroute :
      (∑ x ∈ Ωactive.attach,
        ∑ i ∈ split x,
          (β / 6) *
            edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
              (route x i)) ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := by
    exact
      edgeCopySourcePairDataWeight_finset_attach_splitSum_route_beta_div_six_le_sourcePairSum_of_injOn
        (G := G) hβ (J := fun _ => (1 : ℝ)) (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) Ωactive split route hinj
  change
    (∑ m ∈ Ωactive, F m) ≤
      (β *
        Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
        6
  calc
    (∑ m ∈ Ωactive, F m) ≤
        ∑ x ∈ Ωactive.attach,
          ∑ i ∈ split x,
            (β / 6) *
              edgeCopySourcePairDataWeight G β (fun _ => (1 : ℝ))
                (route x i) := hpoint_sum
    _ ≤
        (β / 6) *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := hroute
    _ =
        (β *
          Sharpness.sourcePairSum G β (fun _ => (1 : ℝ))
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
          6 := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hsubroute :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact
    ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
        hβ hsubroute.1 v hvwedge hlt hypos e0 hedge Ω,
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
        hβ hsubroute.2 v hvwedge hlt hypos e0 hedge Ω⟩

end Exact3D
end StatMech
