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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part102
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumBoundsAt
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
                (∑ m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v w e0 m) ≤
                    (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum
                      β n v) /
                      6 ∧
                  (∑ m ∈ Ωactive,
                    doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                      β n v w e0 m) ≤
                    (β *
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n w)
                        (doubledBoxInnerPairSource n v w)) /
                      6

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumBoundAt
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
                (∑ m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                    β n v w e0 m) ≤
                    (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum
                      β n v) /
                      6

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumBoundAt
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
                (∑ m ∈ Ωactive,
                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                    β n v w e0 m) ≤
                    (β *
                      Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                        (fun _ => 1)
                        (doubledBoxOriginToInnerEndpointSource n w)
                        (doubledBoxInnerPairSource n v w)) /
                      6

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt
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
                ∃ route :
                    {m : Profile // m ∈ Ωactive} →
                      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                        (doubledBoxOriginToInnerEndpointSource n v)
                        (∅ : Finset (FK.boxVerts 3 (2 * n))),
                  Function.Injective route ∧
                    ∀ m : Profile,
                      ∀ hm : m ∈ Ωactive,
                        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                          β n v w e0 m ≤
                          (β / 6) *
                            edgeCopySourcePairDataWeight
                              (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                              (route ⟨m, hm⟩)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt
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
                ∃ route :
                    {m : Profile // m ∈ Ωactive} →
                      edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                        (doubledBoxOriginToInnerEndpointSource n w)
                        (doubledBoxInnerPairSource n v w),
                  Function.Injective route ∧
                    ∀ m : Profile,
                      ∀ hm : m ∈ Ωactive,
                        doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                          β n v w e0 m ≤
                          (β / 6) *
                            edgeCopySourcePairDataWeight
                              (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                              (route ⟨m, hm⟩)

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSubrouteChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
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
                ∃ Split : Type,
                  ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                    ∃ route :
                        (m : {m : Profile // m ∈ Ωactive}) → Split →
                          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                            (doubledBoxOriginToInnerEndpointSource n v)
                            (∅ : Finset (FK.boxVerts 3 (2 * n))),
                      Set.InjOn
                          (fun p :
                              Sigma
                                (fun _ :
                                  {m : Profile // m ∈ Ωactive} => Split) =>
                            route p.1 p.2)
                          (Ωactive.attach.sigma split) ∧
                        ∀ m : Profile,
                          ∀ hm : m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                              β n v w e0 m ≤
                              ∑ i ∈ split ⟨m, hm⟩,
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ⟨m, hm⟩ i)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
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
                ∃ Split : Type,
                  ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                    ∃ route :
                        (m : {m : Profile // m ∈ Ωactive}) → Split →
                          edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
                            (doubledBoxOriginToInnerEndpointSource n w)
                            (doubledBoxInnerPairSource n v w),
                      Set.InjOn
                          (fun p :
                              Sigma
                                (fun _ :
                                  {m : Profile // m ∈ Ωactive} => Split) =>
                            route p.1 p.2)
                          (Ωactive.attach.sigma split) ∧
                        ∀ m : Profile,
                          ∀ hm : m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                              β n v w e0 m ≤
                              ∑ i ∈ split ⟨m, hm⟩,
                                (β / 6) *
                                  edgeCopySourcePairDataWeight
                                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                    (route ⟨m, hm⟩ i)

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairDataSplitSubrouteChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
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
                ∃ Split : Type,
                  ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                    ∃ profileRoute :
                        (m : {m : Profile // m ∈ Ωactive}) → Split →
                          Profile,
                      ∃ witness :
                          (m : {m : Profile // m ∈ Ωactive}) →
                            (i : Split) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m i)),
                        (∀ m i,
                          witness m i ∈
                            edgeCopySourcePairWitnesses
                              (FK.boxGraph 3 (2 * n))
                              (doubledBoxOriginToInnerEndpointSource n v)
                              (∅ : Finset (FK.boxVerts 3 (2 * n)))
                              (profileRoute m i)) ∧
                          Set.InjOn
                              (fun p :
                                  Sigma
                                    (fun _ :
                                      {m : Profile // m ∈ Ωactive} =>
                                      Split) =>
                                profileRoute p.1 p.2)
                              (Ωactive.attach.sigma split) ∧
                            ∀ m : Profile,
                              ∀ hm : m ∈ Ωactive,
                                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                  β n v w e0 m ≤
                                  ∑ i ∈ split ⟨m, hm⟩,
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute ⟨m, hm⟩ i))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
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
                ∃ Split : Type,
                  ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                    ∃ profileRoute :
                        (m : {m : Profile // m ∈ Ωactive}) → Split →
                          Profile,
                      ∃ witness :
                          (m : {m : Profile // m ∈ Ωactive}) →
                            (i : Split) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m i)),
                        (∀ m i,
                          witness m i ∈
                            edgeCopySourcePairWitnesses
                              (FK.boxGraph 3 (2 * n))
                              (doubledBoxOriginToInnerEndpointSource n w)
                              (doubledBoxInnerPairSource n v w)
                              (profileRoute m i)) ∧
                          Set.InjOn
                              (fun p :
                                  Sigma
                                    (fun _ :
                                      {m : Profile // m ∈ Ωactive} =>
                                      Split) =>
                                profileRoute p.1 p.2)
                              (Ωactive.attach.sigma split) ∧
                            ∀ m : Profile,
                              ∀ hm : m ∈ Ωactive,
                                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                  β n v w e0 m ≤
                                  ∑ i ∈ split ⟨m, hm⟩,
                                    (β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute ⟨m, hm⟩ i))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSplitSubrouteChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
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
                ∃ Split : Type,
                  ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                    ∃ profileRoute :
                        (m : {m : Profile // m ∈ Ωactive}) → Split →
                          Profile,
                      ∃ witness :
                          (m : {m : Profile // m ∈ Ωactive}) →
                            (i : Split) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m i)),
                        (∀ m i,
                          Sharpness.RandomCurrent.sources
                            (Sharpness.FluxEdgeCopy.endsM
                              (FK.boxGraph 3 (2 * n))
                              (profileRoute m i))
                            (witness m i) =
                            doubledBoxOriginToInnerEndpointSource n v) ∧
                          (∀ m i,
                            Sharpness.RandomCurrent.sources
                              (Sharpness.FluxEdgeCopy.endsM
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m i))
                              ((Finset.univ :
                                  Finset
                                    (Sharpness.FluxEdgeCopy.Copy
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute m i))) \
                                witness m i) =
                              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                            Set.InjOn
                                (fun p :
                                    Sigma
                                      (fun _ :
                                        {m : Profile // m ∈ Ωactive} =>
                                        Split) =>
                                  profileRoute p.1 p.2)
                                (Ωactive.attach.sigma split) ∧
                              ∀ m : Profile,
                                ∀ hm : m ∈ Ωactive,
                                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                    β n v w e0 m ≤
                                    ∑ i ∈ split ⟨m, hm⟩,
                                      (β / 6) *
                                        Sharpness.weight
                                          (FK.boxGraph 3 (2 * n)) β
                                          (fun _ => 1)
                                          (Sharpness.ofEdgeFun
                                            (FK.boxGraph 3 (2 * n))
                                            (profileRoute ⟨m, hm⟩ i))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
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
                ∃ Split : Type,
                  ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                    ∃ profileRoute :
                        (m : {m : Profile // m ∈ Ωactive}) → Split →
                          Profile,
                      ∃ witness :
                          (m : {m : Profile // m ∈ Ωactive}) →
                            (i : Split) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m i)),
                        (∀ m i,
                          Sharpness.RandomCurrent.sources
                            (Sharpness.FluxEdgeCopy.endsM
                              (FK.boxGraph 3 (2 * n))
                              (profileRoute m i))
                            (witness m i) =
                            doubledBoxOriginToInnerEndpointSource n w) ∧
                          (∀ m i,
                            Sharpness.RandomCurrent.sources
                              (Sharpness.FluxEdgeCopy.endsM
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m i))
                              ((Finset.univ :
                                  Finset
                                    (Sharpness.FluxEdgeCopy.Copy
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute m i))) \
                                witness m i) =
                              doubledBoxInnerPairSource n v w) ∧
                            Set.InjOn
                                (fun p :
                                    Sigma
                                      (fun _ :
                                        {m : Profile // m ∈ Ωactive} =>
                                        Split) =>
                                  profileRoute p.1 p.2)
                                (Ωactive.attach.sigma split) ∧
                              ∀ m : Profile,
                                ∀ hm : m ∈ Ωactive,
                                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                    β n v w e0 m ≤
                                    ∑ i ∈ split ⟨m, hm⟩,
                                      (β / 6) *
                                        Sharpness.weight
                                          (FK.boxGraph 3 (2 * n)) β
                                          (fun _ => 1)
                                          (Sharpness.ofEdgeFun
                                            (FK.boxGraph 3 (2 * n))
                                            (profileRoute ⟨m, hm⟩ i))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSplitSubrouteChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundAt
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
              ∀ Ωactive : Finset Profile,
                (∀ m : Profile,
                  ∀ hm : m ∈ Ωactive,
                    doubledBoxIncrementedFullSourceActive n w e0 m) →
                  Ωactive.Nonempty →
                    ∃ Split : Type,
                      ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                        ∃ profileRoute :
                            (m : {m : Profile // m ∈ Ωactive}) → Split →
                              Profile,
                          ∃ witness :
                              (m : {m : Profile // m ∈ Ωactive}) →
                                (i : Split) →
                                Finset
                                  (Sharpness.FluxEdgeCopy.Copy
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute m i)),
                            (∀ m i,
                              Sharpness.RandomCurrent.sources
                                (Sharpness.FluxEdgeCopy.endsM
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m i))
                                (witness m i) =
                                doubledBoxOriginToInnerEndpointSource n v) ∧
                              (∀ m i,
                                Sharpness.RandomCurrent.sources
                                  (Sharpness.FluxEdgeCopy.endsM
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute m i))
                                  ((Finset.univ :
                                      Finset
                                        (Sharpness.FluxEdgeCopy.Copy
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute m i))) \
                                    witness m i) =
                                  (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                                Set.InjOn
                                    (fun p :
                                        Sigma
                                          (fun _ :
                                            {m : Profile // m ∈ Ωactive} =>
                                            Split) =>
                                      profileRoute p.1 p.2)
                                    (Ωactive.attach.sigma split) ∧
                                  ∀ m : Profile,
                                    ∀ hm : m ∈ Ωactive,
                                      doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                        β n v w e0 m ≤
                                        ∑ i ∈ split ⟨m, hm⟩,
                                          (β / 6) *
                                            Sharpness.weight
                                              (FK.boxGraph 3 (2 * n)) β
                                              (fun _ => 1)
                                              (Sharpness.ofEdgeFun
                                                (FK.boxGraph 3 (2 * n))
                                                (profileRoute ⟨m, hm⟩ i))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundAt
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
              ∀ Ωactive : Finset Profile,
                (∀ m : Profile,
                  ∀ hm : m ∈ Ωactive,
                    doubledBoxIncrementedFullSourceActive n w e0 m) →
                  Ωactive.Nonempty →
                    ∃ Split : Type,
                      ∃ split : {m : Profile // m ∈ Ωactive} → Finset Split,
                        ∃ profileRoute :
                            (m : {m : Profile // m ∈ Ωactive}) → Split →
                              Profile,
                          ∃ witness :
                              (m : {m : Profile // m ∈ Ωactive}) →
                                (i : Split) →
                                Finset
                                  (Sharpness.FluxEdgeCopy.Copy
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute m i)),
                            (∀ m i,
                              Sharpness.RandomCurrent.sources
                                (Sharpness.FluxEdgeCopy.endsM
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m i))
                                (witness m i) =
                                doubledBoxOriginToInnerEndpointSource n w) ∧
                              (∀ m i,
                                Sharpness.RandomCurrent.sources
                                  (Sharpness.FluxEdgeCopy.endsM
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute m i))
                                  ((Finset.univ :
                                      Finset
                                        (Sharpness.FluxEdgeCopy.Copy
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute m i))) \
                                    witness m i) =
                                  doubledBoxInnerPairSource n v w) ∧
                                Set.InjOn
                                    (fun p :
                                        Sigma
                                          (fun _ :
                                            {m : Profile // m ∈ Ωactive} =>
                                            Split) =>
                                      profileRoute p.1 p.2)
                                    (Ωactive.attach.sigma split) ∧
                                  ∀ m : Profile,
                                    ∀ hm : m ∈ Ωactive,
                                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                        β n v w e0 m ≤
                                        ∑ i ∈ split ⟨m, hm⟩,
                                          (β / 6) *
                                            Sharpness.weight
                                              (FK.boxGraph 3 (2 * n)) β
                                              (fun _ => 1)
                                              (Sharpness.ofEdgeFun
                                                (FK.boxGraph 3 (2 * n))
                                                (profileRoute ⟨m, hm⟩ i))

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSplitSubrouteChargeBoundAt
      β n

end Exact3D
end StatMech
