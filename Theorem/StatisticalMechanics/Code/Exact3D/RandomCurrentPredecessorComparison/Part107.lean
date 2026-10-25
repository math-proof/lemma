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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part99
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumChargeBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveCharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
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
  rcases hactiveCharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowCharge, hpoint, htotal⟩
  refine ⟨rowCharge, ?_, ?_⟩
  · intro m hm
    exact hpoint m (Finset.mem_filter.mp hm).1
  · have hΩtouch : Ωtouch = Ωactive := by
      simpa [Ωtouch, Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
    change
      (∑ m ∈ Ωtouch, rowCharge m) ≤
        doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v
    calc
      (∑ m ∈ Ωtouch, rowCharge m) =
          ∑ m ∈ Ωactive, rowCharge m := by rw [hΩtouch]
      _ ≤ doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumChargeBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveCharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
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
  rcases hactiveCharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowCharge, hpoint, htotal⟩
  refine ⟨rowCharge, ?_, ?_⟩
  · intro m hm
    exact hpoint m (Finset.mem_filter.mp hm).1
  · have hΩtouch : Ωtouch = Ωactive := by
      simpa [Ωtouch, Ωactive, w] using
        doubledBoxIncrementedFullSourceActive_filter_originTouchesEdgeSupport_eq_self_of_strictSectorYPredecessor3
          (n := n) (v := v) hvwedge hlt hypos (e0 := e0) hedge Ω
    change
      (∑ m ∈ Ωtouch, rowCharge m) ≤
        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w)
    calc
      (∑ m ∈ Ωtouch, rowCharge m) =
          ∑ m ∈ Ωactive, rowCharge m := by rw [hΩtouch]
      _ ≤
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n w)
            (doubledBoxInnerPairSource n v w) := htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_activeResidualBranchSixthFiniteSumChargeBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveCharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumChargeBoundAt
      hactiveCharge.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumChargeBoundAt
      hactiveCharge.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundAt_of_activeResidualBranchEmptySixthFiniteSumChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hcharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowCharge, hpoint, htotal⟩
  refine ⟨fun m => (β / 6) * rowCharge m, hpoint, ?_⟩
  have hcoef : 0 ≤ β / 6 := by positivity
  calc
    (∑ m ∈
        Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
        (β / 6) * rowCharge m) =
        (β / 6) *
          ∑ m ∈
            Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
            rowCharge m := by
      rw [Finset.mul_sum]
    _ ≤
        (β / 6) *
          doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
      mul_le_mul_of_nonneg_left htotal hcoef
    _ =
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hcharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowCharge, hpoint, htotal⟩
  refine ⟨fun m => (β / 6) * rowCharge m, hpoint, ?_⟩
  have hcoef : 0 ≤ β / 6 := by positivity
  calc
    (∑ m ∈
        Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
        (β / 6) * rowCharge m) =
        (β / 6) *
          ∑ m ∈
            Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0),
            rowCharge m := by
      rw [Finset.mul_sum]
    _ ≤
        (β / 6) *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
      mul_le_mul_of_nonneg_left htotal hcoef
    _ =
        (β *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) /
          6 := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt_of_activeResidualBranchSixthFiniteSumChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumMajorantBoundAt_of_activeResidualBranchEmptySixthFiniteSumChargeBoundAt
      hβ hcharge.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumMajorantBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumChargeBoundAt
      hβ hcharge.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt_of_activeResidualBranchEmptyInnerSixthFiniteSumChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumMajorantBoundsAt_of_activeResidualBranchSixthFiniteSumChargeBoundsAt
    hβ ⟨hempty, hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  rcases hdata v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine
    ⟨fun m =>
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (route m),
      ?_, ?_⟩
  · simpa [Ωactive, w] using hpoint
  · simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum, Ωactive, w] using
      edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
        (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωactive route hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  rcases hdata v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine
    ⟨fun m =>
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (route m),
      ?_, ?_⟩
  · simpa [Ωactive, w] using hpoint
  · simpa [Ωactive, w] using
      edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
        (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) Ωactive route hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    (hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      hβ hdata.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      hβ hdata.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveData :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
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
  rcases hactiveData v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine ⟨route, ?_, ?_⟩
  · intro a ha b hb hab
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  · intro m hm
    exact hpoint m (Finset.mem_filter.mp hm).1

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveData :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
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
  rcases hactiveData v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine ⟨route, ?_, ?_⟩
  · intro a ha b hb hab
    exact hinj (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1 hab
  · intro m hm
    exact hpoint m (Finset.mem_filter.mp hm).1

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt_of_activeResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hactiveData :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      hactiveData.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt_of_activeResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      hactiveData.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt_of_residualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
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
  rcases hdata v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine
    ⟨fun m =>
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (route m),
      ?_, ?_⟩
  · simpa [Ωtouch, w] using hpoint
  · simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum, Ωtouch, w] using
      edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
        (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωtouch route hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_residualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
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
  rcases hdata v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine
    ⟨fun m =>
      edgeCopySourcePairDataWeight (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (route m),
      ?_, ?_⟩
  · simpa [Ωtouch, w] using hpoint
  · simpa [Ωtouch, w] using
      edgeCopySourcePairDataWeight_finset_sum_route_le_sourcePairSum_of_injOn
        (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
        (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) Ωtouch route hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_residualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hdata :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt_of_residualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
      hβ hdata.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_residualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
      hβ hdata.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_residualBranchEmptyInnerSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_residualBranchSixthFiniteSumSourcePairDataInjectionChargeBoundsAt
    hβ ⟨hempty, hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt_of_residualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hinjection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
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
  rcases hinjection v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine
    ⟨fun m =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) (route m),
      ?_, ?_⟩
  · simpa [Ωtouch, w] using hpoint
  · simpa [doubledBoxOriginToInnerEndpointSourcePairEmptySum, Ωtouch, w] using
      edgeCopySourcePairSummand_finset_sum_route_le_sourcePairSum_of_injOn
        (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
        (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n v)
        (∅ : Finset (FK.boxVerts 3 (2 * n))) Ωtouch route hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_residualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hinjection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
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
  rcases hinjection v hvwedge hlt hypos e0 hedge Ω with
    ⟨route, hinj, hpoint⟩
  refine
    ⟨fun m =>
      edgeCopySourcePairSummand (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) (route m),
      ?_, ?_⟩
  · simpa [Ωtouch, w] using hpoint
  · simpa [Ωtouch, w] using
      edgeCopySourcePairSummand_finset_sum_route_le_sourcePairSum_of_injOn
        (G := FK.boxGraph 3 (2 * n)) hβ (J := fun _ => 1)
        (by intro e; norm_num)
        (doubledBoxOriginToInnerEndpointSource n w)
        (doubledBoxInnerPairSource n v w) Ωtouch route hinj

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_residualBranchSixthFiniteSumSourcePairInjectionChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hinjection :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumSourcePairInjectionChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt_of_residualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundAt
      hβ hinjection.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt_of_residualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundAt
      hβ hinjection.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_residualBranchEmptyInnerSixthFiniteSumSourcePairInjectionChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumSourcePairInjectionChargeBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumSourcePairInjectionChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt_of_residualBranchSixthFiniteSumSourcePairInjectionChargeBoundsAt
    hβ ⟨hempty, hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt_of_residualBranchEmptySixthFiniteSumChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hcharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowCharge, hpoint, htotal⟩
  refine ⟨fun m => (β / 6) * rowCharge m, hpoint, ?_⟩
  have hcoef : 0 ≤ β / 6 := by positivity
  calc
    (∑ m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        (β / 6) * rowCharge m) =
        (β / 6) *
          ∑ m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
              (fun m => doubledBoxOriginTouchesEdgeSupport n m),
            rowCharge m := by
      rw [Finset.mul_sum]
    _ ≤
        (β / 6) *
          doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v :=
      mul_le_mul_of_nonneg_left htotal hcoef
    _ =
        (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum β n v) / 6 := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt_of_residualBranchInnerPairSixthFiniteSumChargeBoundAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hcharge v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowCharge, hpoint, htotal⟩
  refine ⟨fun m => (β / 6) * rowCharge m, hpoint, ?_⟩
  have hcoef : 0 ≤ β / 6 := by positivity
  calc
    (∑ m ∈
        (Ω.filter
          (doubledBoxIncrementedFullSourceActive n
            (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
          (fun m => doubledBoxOriginTouchesEdgeSupport n m),
        (β / 6) * rowCharge m) =
        (β / 6) *
          ∑ m ∈
            (Ω.filter
              (doubledBoxIncrementedFullSourceActive n
                (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos) e0)).filter
              (fun m => doubledBoxOriginTouchesEdgeSupport n m),
            rowCharge m := by
      rw [Finset.mul_sum]
    _ ≤
        (β / 6) *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos)) :=
      mul_le_mul_of_nonneg_left htotal hcoef
    _ =
        (β *
          Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
            (doubledBoxOriginToInnerEndpointSource n
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))
            (doubledBoxInnerPairSource n v
              (boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos))) /
          6 := by
      ring

set_option linter.style.longLine false in

theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt_of_residualBranchSixthFiniteSumChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hcharge :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumChargeBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt
      β n :=
  ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt_of_residualBranchEmptySixthFiniteSumChargeBoundAt
      hβ hcharge.1,
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt_of_residualBranchInnerPairSixthFiniteSumChargeBoundAt
      hβ hcharge.2⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt_of_residualBranchEmptyInnerSixthFiniteSumChargeBoundsAt
    {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumChargeBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumChargeBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt_of_residualBranchSixthFiniteSumChargeBoundsAt
    hβ ⟨hempty, hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt_of_residualBranchEmptySixthFiniteSumMajorantBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hmajorant v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowBudget, hpoint, htotal⟩
  exact (Finset.sum_le_sum (fun m hm => hpoint m hm)).trans htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt_of_residualBranchInnerPairSixthFiniteSumMajorantBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  rcases hmajorant v hvwedge hlt hypos e0 hedge Ω with
    ⟨rowBudget, hpoint, htotal⟩
  exact (Finset.sum_le_sum (fun m hm => hpoint m hm)).trans htotal

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt_of_residualBranchSixthFiniteSumMajorantBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hmajorant :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumMajorantBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact
    ⟨freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt_of_residualBranchEmptySixthFiniteSumMajorantBoundAt
        hmajorant.1 v hvwedge hlt hypos e0 hedge Ω,
      freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt_of_residualBranchInnerPairSixthFiniteSumMajorantBoundAt
        hmajorant.2 v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt_of_residualBranchEmptyInnerSixthFiniteSumMajorantBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumMajorantBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumMajorantBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
      β n :=
  freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt_of_residualBranchSixthFiniteSumMajorantBoundsAt
    ⟨hempty, hinner⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt_of_emptyBoundAt_innerPairBoundAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hempty :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt
        β n)
    (hinner :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact
    ⟨hempty v hvwedge hlt hypos e0 hedge Ω,
      hinner v hvwedge hlt hypos e0 hedge Ω⟩

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt_of_residualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchEmptySixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact (hbounds v hvwedge hlt hypos e0 hedge Ω).1

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt_of_residualBranchSixthFiniteSumBoundsAt
    {β : ℝ} {n : ℕ}
    [DecidablePred
      (fun m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ =>
        doubledBoxOriginTouchesEdgeSupport n m)]
    (hbounds :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchSixthFiniteSumBoundsAt
        β n) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginTouchesEdgeSupportResidualBranchInnerPairSixthFiniteSumBoundAt
      β n := by
  intro v hvwedge hlt hypos
  dsimp only
  intro e0 hedge Ω
  exact (hbounds v hvwedge hlt hypos e0 hedge Ω).2

end Exact3D
end StatMech
