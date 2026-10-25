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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part97
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ ew' ∈ doubledBoxOriginIncidentEdges n,
                            ew ≠ ew' →
                              ∀ m ∈ Ωactive.filter
                                  (fun m => ownerOf m = ew),
                                ∀ m' ∈ Ωactive.filter
                                    (fun m => ownerOf m = ew'),
                                  route ew m ≠ route ew' m') ∧
                          ∀ m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route (ownerOf m) m)

open Classical in
set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                      ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ ew' ∈ doubledBoxOriginIncidentEdges n,
                            ew ≠ ew' →
                              ∀ m ∈ Ωactive.filter
                                  (fun m => ownerOf m = ew),
                                ∀ m' ∈ Ωactive.filter
                                    (fun m => ownerOf m = ew'),
                                  route ew m ≠ route ew' m') ∧
                          ∀ m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route (ownerOf m) m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerRouteBoundAt
      β n

open Classical in
set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      ∃ tag :
                          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                            (doubledBoxOriginToInnerEndpointSource n v)
                            (∅ : Finset (FK.boxVerts 3 (2 * n))) →
                            Edge,
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          Set.InjOn (route ew)
                            (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                          (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m => ownerOf m = ew),
                              tag (route ew m) = ew) ∧
                            ∀ m ∈ Ωactive,
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route (ownerOf m) m)

open Classical in
set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      ∃ tag :
                          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                            (doubledBoxOriginToInnerEndpointSource n w)
                            (doubledBoxInnerPairSource n v w) →
                            Edge,
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          Set.InjOn (route ew)
                            (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                          (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                            ∀ m ∈ Ωactive.filter
                                (fun m => ownerOf m = ew),
                              tag (route ew m) = ew) ∧
                            ∀ m ∈ Ωactive,
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route (ownerOf m) m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerTaggedRouteBoundAt
      β n

open Classical in
set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m => ownerOf m = ew),
                            doubledBoxOriginIncidentOwner n (route ew m).1 =
                              some ew) ∧
                          ∀ m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route (ownerOf m) m)

open Classical in
set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m => ownerOf m = ew),
                            doubledBoxOriginIncidentOwner n (route ew m).1 =
                              some ew) ∧
                          ∀ m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route (ownerOf m) m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerProfileTaggedRouteBoundAt
      β n

open Classical in
set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m => ownerOf m = ew),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route (ownerOf m) m)

open Classical in
set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
    (β : ℝ) (n : ℕ) : Prop :=
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
                  Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
                ∃ ownerOf : Profile → Edge,
                  (∀ m ∈ Ωactive,
                    ownerOf m ∈ doubledBoxOriginIncidentEdges n ∧
                      doubledBoxOriginIncidentOwner n m =
                        some (ownerOf m)) ∧
                    ∃ route : Edge → Profile →
                        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w),
                      (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                        Set.InjOn (route ew)
                          (Ωactive.filter (fun m => ownerOf m = ew))) ∧
                        (∀ ew ∈ doubledBoxOriginIncidentEdges n,
                          ∀ m ∈ Ωactive.filter
                              (fun m => ownerOf m = ew),
                            doubledBoxOriginIncidentSupport n
                              (route ew m).1 = {ew}) ∧
                          ∀ m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                edgeCopySourcePairDataWeight
                                  (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                  (route (ownerOf m) m)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataInjectionOwnerSupportSingletonRouteBoundAt
      β n

end Exact3D
end StatMech
