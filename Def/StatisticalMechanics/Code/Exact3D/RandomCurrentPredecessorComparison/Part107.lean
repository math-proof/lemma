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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part114
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def ExactSupportOwnerResidualSourcePairSourceEquationRouteShareBoundsAt
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
                let supportPatterns : Finset (Finset Edge) :=
                  Finset.filter (fun S => S.Nonempty)
                    (Finset.powerset (doubledBoxOriginIncidentEdges n))
                (∀ S ∈ supportPatterns,
                  ∀ ew ∈ S,
                    ∃ profileRoute : Profile → Profile,
                      ∃ witness :
                          (m : Profile) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m)),
                        Set.InjOn profileRoute
                            (Ωactive.filter
                              (fun m =>
                                doubledBoxOriginIncidentSupport n m = S ∧
                                  doubledBoxOriginIncidentOwner n m =
                                    some ew)) ∧
                          (∀ m,
                            Sharpness.RandomCurrent.sources
                              (Sharpness.FluxEdgeCopy.endsM
                                (FK.boxGraph 3 (2 * n))
                                (profileRoute m))
                              (witness m) =
                              doubledBoxOriginToInnerEndpointSource n v) ∧
                            (∀ m,
                              Sharpness.RandomCurrent.sources
                                (Sharpness.FluxEdgeCopy.endsM
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m))
                                ((Finset.univ :
                                    Finset
                                      (Sharpness.FluxEdgeCopy.Copy
                                        (FK.boxGraph 3 (2 * n))
                                        (profileRoute m))) \
                                  witness m) =
                                (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                              ∀ m ∈ Ωactive.filter
                                  (fun m =>
                                    doubledBoxOriginIncidentSupport n m = S ∧
                                      doubledBoxOriginIncidentOwner n m =
                                        some ew),
                                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                  β n v w e0 m ≤
                                  ((β / 6) *
                                    Sharpness.weight
                                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                                      (Sharpness.ofEdgeFun
                                        (FK.boxGraph 3 (2 * n))
                                        (profileRoute m))) /
                                    384) ∧
                  (∀ S ∈ supportPatterns,
                    ∀ ew ∈ S,
                      ∃ profileRoute : Profile → Profile,
                        ∃ witness :
                            (m : Profile) →
                              Finset
                                (Sharpness.FluxEdgeCopy.Copy
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m)),
                          Set.InjOn profileRoute
                              (Ωactive.filter
                                (fun m =>
                                  doubledBoxOriginIncidentSupport n m = S ∧
                                    doubledBoxOriginIncidentOwner n m =
                                      some ew)) ∧
                            (∀ m,
                              Sharpness.RandomCurrent.sources
                                (Sharpness.FluxEdgeCopy.endsM
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m))
                                (witness m) =
                                doubledBoxOriginToInnerEndpointSource n w) ∧
                              (∀ m,
                                Sharpness.RandomCurrent.sources
                                  (Sharpness.FluxEdgeCopy.endsM
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute m))
                                  ((Finset.univ :
                                      Finset
                                        (Sharpness.FluxEdgeCopy.Copy
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute m))) \
                                    witness m) =
                                  doubledBoxInnerPairSource n v w) ∧
                                ∀ m ∈ Ωactive.filter
                                    (fun m =>
                                      doubledBoxOriginIncidentSupport n m =
                                          S ∧
                                        doubledBoxOriginIncidentOwner n m =
                                          some ew),
                                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                    β n v w e0 m ≤
                                    ((β / 6) *
                                      Sharpness.weight
                                        (FK.boxGraph 3 (2 * n)) β
                                        (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute m))) /
                                      384)

open Classical in
set_option linter.style.longLine false in


def ExactSupportOwnerResidualSourcePairEmptySourceEquationCellRouteShareBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  ∃ profileRoute : Profile → Profile,
    ∃ witness :
        (m : Profile) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (profileRoute m)),
      Set.InjOn profileRoute
          (Ωactive.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew)) ∧
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n))
              (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n v) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n))
                (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) \
                witness m) =
              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
            ∀ m ∈ Ωactive.filter
                (fun m =>
                  doubledBoxOriginIncidentSupport n m = S ∧
                    doubledBoxOriginIncidentOwner n m = some ew),
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                β n v w e0 m ≤
                ((β / 6) *
                  Sharpness.weight
                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (Sharpness.ofEdgeFun
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) /
                  384

open Classical in
set_option linter.style.longLine false in


def ExactSupportOwnerResidualSourcePairInnerPairSourceEquationCellRouteShareBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  ∃ profileRoute : Profile → Profile,
    ∃ witness :
        (m : Profile) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (profileRoute m)),
      Set.InjOn profileRoute
          (Ωactive.filter
            (fun m =>
              doubledBoxOriginIncidentSupport n m = S ∧
                doubledBoxOriginIncidentOwner n m = some ew)) ∧
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n))
              (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n w) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n))
                (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) \
                witness m) =
              doubledBoxInnerPairSource n v w) ∧
            ∀ m ∈ Ωactive.filter
                (fun m =>
                  doubledBoxOriginIncidentSupport n m = S ∧
                    doubledBoxOriginIncidentOwner n m = some ew),
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v w e0 m ≤
                ((β / 6) *
                  Sharpness.weight
                    (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                    (Sharpness.ofEdgeFun
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) /
                  384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ profileRoute : {m : Profile // m ∈ cell} → Profile,
    ∃ witness :
        (m : {m : Profile // m ∈ cell}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (profileRoute m)),
      Function.Injective profileRoute ∧
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n))
              (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n v) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n))
                (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) \
                witness m) =
              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
            ∀ m : Profile,
              ∀ hm : m ∈ cell,
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                  β n v w e0 m ≤
                  ((β / 6) *
                    Sharpness.weight
                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                      (Sharpness.ofEdgeFun
                        (FK.boxGraph 3 (2 * n))
                        (profileRoute ⟨m, hm⟩))) /
                    384

open Classical in
set_option linter.style.longLine false in

def
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ profileRoute : {m : Profile // m ∈ cell} → Profile,
    ∃ witness :
        (m : {m : Profile // m ∈ cell}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (profileRoute m)),
      Function.Injective profileRoute ∧
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n))
              (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n w) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n))
                (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) \
                witness m) =
              doubledBoxInnerPairSource n v w) ∧
            ∀ m : Profile,
              ∀ hm : m ∈ cell,
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                  β n v w e0 m ≤
                  ((β / 6) *
                    Sharpness.weight
                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                      (Sharpness.ofEdgeFun
                        (FK.boxGraph 3 (2 * n))
                        (profileRoute ⟨m, hm⟩))) /
                      384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ Split : Type,
    ∃ split : {m : Profile // m ∈ cell} → Finset Split,
      ∃ route :
          (m : {m : Profile // m ∈ cell}) → Split →
            edgeCopySourcePairData G
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))),
        Set.InjOn
            (fun p :
                Sigma (fun _ : {m : Profile // m ∈ cell} => Split) =>
              route p.1 p.2)
            (cell.attach.sigma split) ∧
          ∀ m : Profile,
            ∀ hm : m ∈ cell,
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                β n v w e0 m ≤
                ∑ i ∈ split ⟨m, hm⟩,
                  ((β / 6) *
                    edgeCopySourcePairDataWeight G β (fun _ => 1)
                      (route ⟨m, hm⟩ i)) /
                    384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ Split : Type,
    ∃ split : {m : Profile // m ∈ cell} → Finset Split,
      ∃ route :
          (m : {m : Profile // m ∈ cell}) → Split →
            edgeCopySourcePairData G
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w),
        Set.InjOn
            (fun p :
                Sigma (fun _ : {m : Profile // m ∈ cell} => Split) =>
              route p.1 p.2)
            (cell.attach.sigma split) ∧
          ∀ m : Profile,
            ∀ hm : m ∈ cell,
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                β n v w e0 m ≤
                ∑ i ∈ split ⟨m, hm⟩,
                  ((β / 6) *
                    edgeCopySourcePairDataWeight G β (fun _ => 1)
                      (route ⟨m, hm⟩ i)) /
                    384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptySplitDataFiniteCellRouteShareAtEdgeBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ Split : Type,
    ∃ split : {m : Profile // m ∈ cell} → Finset Split,
      ∃ route :
          (m : {m : Profile // m ∈ cell}) → Split →
            edgeCopySourcePairData G
              (doubledBoxOriginToInnerEndpointSource n v)
              (∅ : Finset (FK.boxVerts 3 (2 * n))),
        Set.InjOn
            (fun p :
                Sigma (fun _ : {m : Profile // m ∈ cell} => Split) =>
              route p.1 p.2)
            (cell.attach.sigma split) ∧
          ∀ m : Profile,
            ∀ hm : m ∈ cell,
              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                β n v w e0 ew m ≤
                ∑ i ∈ split ⟨m, hm⟩,
                  ((β / 6) *
                    edgeCopySourcePairDataWeight G β (fun _ => 1)
                      (route ⟨m, hm⟩ i)) /
                    384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairInnerPairSplitDataFiniteCellRouteShareAtEdgeBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ Split : Type,
    ∃ split : {m : Profile // m ∈ cell} → Finset Split,
      ∃ route :
          (m : {m : Profile // m ∈ cell}) → Split →
            edgeCopySourcePairData G
              (doubledBoxOriginToInnerEndpointSource n w)
              (doubledBoxInnerPairSource n v w),
        Set.InjOn
            (fun p :
                Sigma (fun _ : {m : Profile // m ∈ cell} => Split) =>
              route p.1 p.2)
            (cell.attach.sigma split) ∧
          ∀ m : Profile,
            ∀ hm : m ∈ cell,
              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                β n v w e0 ew m ≤
                ∑ i ∈ split ⟨m, hm⟩,
                  ((β / 6) *
                    edgeCopySourcePairDataWeight G β (fun _ => 1)
                      (route ⟨m, hm⟩ i)) /
                    384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptySourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ profileRoute : {m : Profile // m ∈ cell} → Profile,
    ∃ witness :
        (m : {m : Profile // m ∈ cell}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (profileRoute m)),
      Function.Injective profileRoute ∧
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n))
              (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n v) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n))
                (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) \
                witness m) =
              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
            ∀ m : Profile,
              ∀ hm : m ∈ cell,
                doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                  β n v w e0 ew m ≤
                  ((β / 6) *
                    Sharpness.weight
                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                      (Sharpness.ofEdgeFun
                        (FK.boxGraph 3 (2 * n))
                        (profileRoute ⟨m, hm⟩))) /
                    384

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairInnerPairSourceEquationFiniteCellRouteShareAtEdgeBoundsAt
    (β : ℝ) (n : ℕ)
    (v : FK.boxVerts 3 n)
    (hvwedge : boxVertPositiveXFaceOrderedWedge3 n v)
    (hlt :
      ((v : Lattice.Site 3) (1 : Fin 3)) <
        ((v : Lattice.Site 3) (2 : Fin 3)))
    (hypos : 0 < ((v : Lattice.Site 3) (1 : Fin 3)))
    (e0 : ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (Ω : Finset (↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ))
    (S : Finset ↥(FK.boxGraph 3 (2 * n)).edgeFinset)
    (ew : ↥(FK.boxGraph 3 (2 * n)).edgeFinset) : Prop :=
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
  ∃ profileRoute : {m : Profile // m ∈ cell} → Profile,
    ∃ witness :
        (m : {m : Profile // m ∈ cell}) →
          Finset
            (Sharpness.FluxEdgeCopy.Copy
              (FK.boxGraph 3 (2 * n))
              (profileRoute m)),
      Function.Injective profileRoute ∧
        (∀ m,
          Sharpness.RandomCurrent.sources
            (Sharpness.FluxEdgeCopy.endsM
              (FK.boxGraph 3 (2 * n))
              (profileRoute m))
            (witness m) =
            doubledBoxOriginToInnerEndpointSource n w) ∧
          (∀ m,
            Sharpness.RandomCurrent.sources
              (Sharpness.FluxEdgeCopy.endsM
                (FK.boxGraph 3 (2 * n))
                (profileRoute m))
              ((Finset.univ :
                  Finset
                    (Sharpness.FluxEdgeCopy.Copy
                      (FK.boxGraph 3 (2 * n))
                      (profileRoute m))) \
                witness m) =
              doubledBoxInnerPairSource n v w) ∧
            ∀ m : Profile,
              ∀ hm : m ∈ cell,
                doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                  β n v w e0 ew m ≤
                  ((β / 6) *
                    Sharpness.weight
                      (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                      (Sharpness.ofEdgeFun
                        (FK.boxGraph 3 (2 * n))
                        (profileRoute ⟨m, hm⟩))) /
                    384

end Exact3D
end StatMech
