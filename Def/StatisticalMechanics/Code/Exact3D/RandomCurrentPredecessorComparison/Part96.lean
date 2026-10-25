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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part103
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
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
                ∃ profileRoute :
                    {m : Profile // m ∈ Ωactive} → Profile,
                  ∃ witness :
                      (m : {m : Profile // m ∈ Ωactive}) →
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n)) (profileRoute m)),
                    (∀ m,
                      witness m ∈
                        edgeCopySourcePairWitnesses
                          (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n v)
                          (∅ : Finset (FK.boxVerts 3 (2 * n)))
                          (profileRoute m)) ∧
                      Function.Injective profileRoute ∧
                        ∀ m : Profile,
                          ∀ hm : m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                                  (fun _ => 1)
                                  (Sharpness.ofEdgeFun
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute ⟨m, hm⟩))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
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
                ∃ profileRoute :
                    {m : Profile // m ∈ Ωactive} → Profile,
                  ∃ witness :
                      (m : {m : Profile // m ∈ Ωactive}) →
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n)) (profileRoute m)),
                    (∀ m,
                      witness m ∈
                        edgeCopySourcePairWitnesses
                          (FK.boxGraph 3 (2 * n))
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w)
                          (profileRoute m)) ∧
                      Function.Injective profileRoute ∧
                        ∀ m : Profile,
                          ∀ hm : m ∈ Ωactive,
                            doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                              β n v w e0 m ≤
                              (β / 6) *
                                Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                                  (fun _ => 1)
                                  (Sharpness.ofEdgeFun
                                    (FK.boxGraph 3 (2 * n))
                                    (profileRoute ⟨m, hm⟩))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairProfileWitnessSubrouteChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
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
                ∃ profileRoute :
                    {m : Profile // m ∈ Ωactive} → Profile,
                  ∃ witness :
                      (m : {m : Profile // m ∈ Ωactive}) →
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n)) (profileRoute m)),
                    (∀ m,
                      Sharpness.RandomCurrent.sources
                        (Sharpness.FluxEdgeCopy.endsM
                          (FK.boxGraph 3 (2 * n)) (profileRoute m))
                        (witness m) =
                        doubledBoxOriginToInnerEndpointSource n v) ∧
                      (∀ m,
                        Sharpness.RandomCurrent.sources
                          (Sharpness.FluxEdgeCopy.endsM
                            (FK.boxGraph 3 (2 * n)) (profileRoute m))
                          ((Finset.univ :
                              Finset
                                (Sharpness.FluxEdgeCopy.Copy
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m))) \
                            witness m) =
                          (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                        Function.Injective profileRoute ∧
                          ∀ m : Profile,
                            ∀ hm : m ∈ Ωactive,
                              doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                                    (fun _ => 1)
                                    (Sharpness.ofEdgeFun
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute ⟨m, hm⟩))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
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
                ∃ profileRoute :
                    {m : Profile // m ∈ Ωactive} → Profile,
                  ∃ witness :
                      (m : {m : Profile // m ∈ Ωactive}) →
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n)) (profileRoute m)),
                    (∀ m,
                      Sharpness.RandomCurrent.sources
                        (Sharpness.FluxEdgeCopy.endsM
                          (FK.boxGraph 3 (2 * n)) (profileRoute m))
                        (witness m) =
                        doubledBoxOriginToInnerEndpointSource n w) ∧
                      (∀ m,
                        Sharpness.RandomCurrent.sources
                          (Sharpness.FluxEdgeCopy.endsM
                            (FK.boxGraph 3 (2 * n)) (profileRoute m))
                          ((Finset.univ :
                              Finset
                                (Sharpness.FluxEdgeCopy.Copy
                                  (FK.boxGraph 3 (2 * n))
                                  (profileRoute m))) \
                            witness m) =
                          doubledBoxInnerPairSource n v w) ∧
                        Function.Injective profileRoute ∧
                          ∀ m : Profile,
                            ∀ hm : m ∈ Ωactive,
                              doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                β n v w e0 m ≤
                                (β / 6) *
                                  Sharpness.weight (FK.boxGraph 3 (2 * n)) β
                                    (fun _ => 1)
                                    (Sharpness.ofEdgeFun
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute ⟨m, hm⟩))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationSubrouteChargeBoundAt
      β n

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
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
                    ∃ profileRoute :
                        {m : Profile // m ∈ Ωactive} → Profile,
                      ∃ witness :
                          (m : {m : Profile // m ∈ Ωactive}) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
                        (∀ m,
                          Sharpness.RandomCurrent.sources
                            (Sharpness.FluxEdgeCopy.endsM
                              (FK.boxGraph 3 (2 * n)) (profileRoute m))
                            (witness m) =
                            doubledBoxOriginToInnerEndpointSource n v) ∧
                          (∀ m,
                            Sharpness.RandomCurrent.sources
                              (Sharpness.FluxEdgeCopy.endsM
                                (FK.boxGraph 3 (2 * n)) (profileRoute m))
                              ((Finset.univ :
                                  Finset
                                    (Sharpness.FluxEdgeCopy.Copy
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute m))) \
                                witness m) =
                              (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                            Function.Injective profileRoute ∧
                              ∀ m : Profile,
                                ∀ hm : m ∈ Ωactive,
                                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight (FK.boxGraph 3 (2 * n))
                                        β (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute ⟨m, hm⟩))

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
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
                    ∃ profileRoute :
                        {m : Profile // m ∈ Ωactive} → Profile,
                      ∃ witness :
                          (m : {m : Profile // m ∈ Ωactive}) →
                            Finset
                              (Sharpness.FluxEdgeCopy.Copy
                                (FK.boxGraph 3 (2 * n)) (profileRoute m)),
                        (∀ m,
                          Sharpness.RandomCurrent.sources
                            (Sharpness.FluxEdgeCopy.endsM
                              (FK.boxGraph 3 (2 * n)) (profileRoute m))
                            (witness m) =
                            doubledBoxOriginToInnerEndpointSource n w) ∧
                          (∀ m,
                            Sharpness.RandomCurrent.sources
                              (Sharpness.FluxEdgeCopy.endsM
                                (FK.boxGraph 3 (2 * n)) (profileRoute m))
                              ((Finset.univ :
                                  Finset
                                    (Sharpness.FluxEdgeCopy.Copy
                                      (FK.boxGraph 3 (2 * n))
                                      (profileRoute m))) \
                                witness m) =
                              doubledBoxInnerPairSource n v w) ∧
                            Function.Injective profileRoute ∧
                              ∀ m : Profile,
                                ∀ hm : m ∈ Ωactive,
                                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                                    β n v w e0 m ≤
                                    (β / 6) *
                                      Sharpness.weight (FK.boxGraph 3 (2 * n))
                                        β (fun _ => 1)
                                        (Sharpness.ofEdgeFun
                                          (FK.boxGraph 3 (2 * n))
                                          (profileRoute ⟨m, hm⟩))

set_option linter.style.longLine false in

def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundsAt
    (β : ℝ) (n : ℕ) : Prop :=
  FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchEmptySixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
      β n ∧
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveResidualBranchInnerPairSixthFiniteSumSourcePairSourceEquationActiveSetSubrouteChargeBoundAt
      β n

end Exact3D
end StatMech
