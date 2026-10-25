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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part127
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffExplicitCaseTableBoundAt_of_emptyFiniteCutoffRelaxedExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffRelaxedExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffExplicitCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBound, relaxedBudget, hcover, hpoint, hrelax,
      htotal⟩
  refine ⟨κ, caseSet, caseOf, relaxedBudget, hcover, ?_, htotal⟩
  intro m hm
  exact (hpoint m hm).trans (hrelax (caseOf m) (hcover m hm))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffExplicitCaseTableBoundAt_of_innerPairFiniteCutoffRelaxedExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffRelaxedExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffExplicitCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, rowBound, relaxedBudget, hcover, hpoint, hrelax,
      htotal⟩
  refine ⟨κ, caseSet, caseOf, relaxedBudget, hcover, ?_, htotal⟩
  intro m hm
  exact (hpoint m hm).trans (hrelax (caseOf m) (hcover m hm))

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffExplicitCaseTableBoundAt_of_emptyFiniteCutoffRelaxedExplicitCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffExplicitCaseTableBoundAt_of_innerPairFiniteCutoffRelaxedExplicitCaseTableBoundAt
      htable.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffCaseTableBoundAt_of_emptyFiniteCutoffExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, caseBudget, hcover, hpoint, htotal⟩
  refine ⟨κ, caseOf, caseBudget, hpoint, ?_⟩
  exact
    finiteSupportCaseBudgetTotal_le_of_finiteSupportExplicitCaseBudgetTotal_le
      Ω caseOf caseSet caseBudget hcover htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffCaseTableBoundAt_of_innerPairFiniteCutoffExplicitCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffExplicitCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffCaseTableBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseSet, caseOf, caseBudget, hcover, hpoint, htotal⟩
  refine ⟨κ, caseOf, caseBudget, hpoint, ?_⟩
  exact
    finiteSupportCaseBudgetTotal_le_of_finiteSupportExplicitCaseBudgetTotal_le
      Ω caseOf caseSet caseBudget hcover htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffCaseTableBoundAt_of_emptyFiniteCutoffExplicitCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffCaseTableBoundAt_of_innerPairFiniteCutoffExplicitCaseTableBoundAt
      htable.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffMajorantBoundAt_of_emptyFiniteCutoffCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseOf, caseBudget, hpoint, htotal⟩
  refine ⟨fun m => caseBudget (caseOf m), hpoint, ?_⟩
  calc
    (∑ m ∈ Ω, caseBudget (caseOf m)) =
        finiteSupportCaseBudgetTotal Ω caseOf caseBudget := by
      exact finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω caseOf
        caseBudget
    _ ≤
        β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffMajorantBoundAt_of_innerPairFiniteCutoffCaseTableBoundAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffCaseTableBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos e0 hedge Ω
  rcases htable v hvwedge hlt hypos e0 hedge Ω with
    ⟨κ, caseOf, caseBudget, hpoint, htotal⟩
  refine ⟨fun m => caseBudget (caseOf m), hpoint, ?_⟩
  calc
    (∑ m ∈ Ω, caseBudget (caseOf m)) =
        finiteSupportCaseBudgetTotal Ω caseOf caseBudget := by
      exact finset_sum_caseBudget_eq_finiteSupportCaseBudgetTotal Ω caseOf
        caseBudget
    _ ≤
        β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
          (doubledBoxInnerPairSource n v
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentEmptyFiniteCutoffMajorantBoundAt_of_emptyFiniteCutoffCaseTableBoundAt
      htable.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentInnerPairFiniteCutoffMajorantBoundAt_of_innerPairFiniteCutoffCaseTableBoundAt
      htable.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffMajorantBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffCaseTableBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffMajorantBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffCaseTableBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffCaseTableBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffMajorantBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 < β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentSelectedCopyFiniteCutoffBoundsAt_of_sourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
      htable)

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (htable :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffRelaxedExplicitCaseTableBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentBoundsAt_of_finiteCutoffExplicitCaseTableBoundsAt
    hβ
    (freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYSourceSectorResidualMomentBranchComponentFiniteCutoffExplicitCaseTableBoundsAt_of_finiteCutoffRelaxedExplicitCaseTableBoundsAt
      htable)

end Exact3D
end StatMech
