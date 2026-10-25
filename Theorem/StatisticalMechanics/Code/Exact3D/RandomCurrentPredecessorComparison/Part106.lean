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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part98
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveBound :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  have hΩtouch : Ωtouch = Ωactive := by
    simpa [Ωtouch, Ωactive, w] using
      doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
  have hbound := hactiveBound v hvwedge hlt hypos e0 hedge Ω
  change
    (∑ m ∈ Ωtouch,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) ≤
      (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6
  calc
    (∑ m ∈ Ωtouch,
      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v w
        e0 m) =
        ∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
            w e0 m := by rw [hΩtouch]
    _ ≤ (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 :=
      hbound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveBound :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  have hΩtouch : Ωtouch = Ωactive := by
    simpa [Ωtouch, Ωactive, w] using
      doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
  have hbound := hactiveBound v hvwedge hlt hypos e0 hedge Ω
  change
    (∑ m ∈ Ωtouch,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) ≤
      (β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
        (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w)) /
        6
  calc
    (∑ m ∈ Ωtouch,
      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n v
        w e0 m) =
        ∑ m ∈ Ωactive,
          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
            β n v w e0 m := by rw [hΩtouch]
    _ ≤
        (β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
          6 := hbound

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt_of_activeResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveBound :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  have hΩtouch : Ωtouch = Ωactive := by
    simpa [Ωtouch, Ωactive, w] using
      doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
        (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
  rcases hactiveBound v hvwedge hlt hypos e0 hedge Ω with
    ⟨hempty, hinner⟩
  constructor
  · change
      (∑ m ∈ Ωtouch,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m) ≤
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6
    calc
      (∑ m ∈ Ωtouch,
        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
          w e0 m) =
          ∑ m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand β n v
              w e0 m := by rw [hΩtouch]
      _ ≤ (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 :=
        hempty
  · change
      (∑ m ∈ Ωtouch,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m) ≤
        (β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
          6
    calc
      (∑ m ∈ Ωtouch,
        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand β n
          v w e0 m) =
          ∑ m ∈ Ωactive,
            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
              β n v w e0 m := by rw [hΩtouch]
      _ ≤
          (β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
            6 := hinner

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumMajorantBoundAt
    {β : ℝ} {n : ℕ}
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hmajorant v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowBudget, hpoint, htotal⟩
  exact (Finset.sum_le_sum (fun m hm => hpoint m hm)).trans htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
    {β : ℝ} {n : ℕ}
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hmajorant v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowBudget, hpoint, htotal⟩
  exact (Finset.sum_le_sum (fun m hm => hpoint m hm)).trans htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt_of_activeResidualBranchSixthFiniteSumMajorantBoundsAt
    {β : ℝ} {n : ℕ}
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact
    ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchEmptySixthFiniteSumMajorantBoundAt
        hmajorant.1 v hvwedge hlt hypos e0 hedge Ω,
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
        hmajorant.2 v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt_of_emptyBoundAt_innerPairBoundAt
    {β : ℝ} {n : ℕ}
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact
    ⟨hempty v hvwedge hlt hypos e0 hedge Ω,
      hinner v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt_of_activeResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact (hbounds v hvwedge hlt hypos e0 hedge Ω).1

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt_of_activeResidualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact (hbounds v hvwedge hlt hypos e0 hedge Ω).2

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt_of_activeResidualBranchEmptySixthFiniteSumMajorantBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveMajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  rcases hactiveMajorant v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowBudget, hpoint, htotal⟩
  refine ⟨rowBudget, ?_, ?_⟩
  · intro m hm
    exact hpoint m (Finset.mem_filter.mp hm).1
  · have hΩtouch : Ωtouch = Ωactive := by
      simpa [Ωtouch, Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
    change
      (∑ m ∈ Ωtouch, rowBudget m) ≤
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6
    calc
      (∑ m ∈ Ωtouch, rowBudget m) =
          ∑ m ∈ Ωactive, rowBudget m := by rw [hΩtouch]
      _ ≤
          (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 :=
        htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveMajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let Ωtouch : Finset Profile :=
    Ωactive.filter (fun m => doubledBoxOriginTouchesEdgeSupport n m)
  rcases hactiveMajorant v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowBudget, hpoint, htotal⟩
  refine ⟨rowBudget, ?_, ?_⟩
  · intro m hm
    exact hpoint m (Finset.mem_filter.mp hm).1
  · have hΩtouch : Ωtouch = Ωactive := by
      simpa [Ωtouch, Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
    change
      (∑ m ∈ Ωtouch, rowBudget m) ≤
        (β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
          (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)) /
          6
    calc
      (∑ m ∈ Ωtouch, rowBudget m) =
          ∑ m ∈ Ωactive, rowBudget m := by rw [hΩtouch]
      _ ≤
          (β * Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
            (fun _ => 1) (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w)) /
            6 := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt_of_activeResidualBranchSixthFiniteSumMajorantBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveMajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt_of_activeResidualBranchEmptySixthFiniteSumMajorantBoundAt
      hactiveMajorant.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
      hactiveMajorant.2⟩

end Exact3D
end StatMech
