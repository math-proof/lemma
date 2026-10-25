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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part118
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptyInnerSourceEquationFiniteCellCoverRouteShareBoundsAt
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
  ∃ rows : Finset Profile,
    (∀ m : Profile,
      m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
        m ∈ rows) ∧
      (∃ emptyProfileRouteRows :
          {m : Profile // m ∈ rows} → Profile,
        ∃ emptyWitnessRows :
            (m : {m : Profile // m ∈ rows}) →
              Finset
                (Sharpness.FluxEdgeCopy.Copy
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m)),
          Function.Injective emptyProfileRouteRows ∧
            (∀ m,
              Sharpness.RandomCurrent.sources
                (Sharpness.FluxEdgeCopy.endsM
                  (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m))
                (emptyWitnessRows m) =
                doubledBoxOriginToInnerEndpointSource n v) ∧
              (∀ m,
                Sharpness.RandomCurrent.sources
                  (Sharpness.FluxEdgeCopy.endsM
                    (FK.boxGraph 3 (2 * n)) (emptyProfileRouteRows m))
                  ((Finset.univ :
                      Finset
                        (Sharpness.FluxEdgeCopy.Copy
                          (FK.boxGraph 3 (2 * n))
                          (emptyProfileRouteRows m))) \
                    emptyWitnessRows m) =
                  (∅ : Finset (FK.boxVerts 3 (2 * n)))) ∧
                ∀ m,
                  ∀ hm : m ∈ rows,
                    doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                        β n v w e0 m ≤
                      ((β / 6) *
                        Sharpness.weight
                          (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                          (Sharpness.ofEdgeFun
                            (FK.boxGraph 3 (2 * n))
                            (emptyProfileRouteRows ⟨m, hm⟩))) /
                        384) ∧
        (∃ innerProfileRouteRows :
            {m : Profile // m ∈ rows} → Profile,
          ∃ innerWitnessRows :
              (m : {m : Profile // m ∈ rows}) →
                Finset
                  (Sharpness.FluxEdgeCopy.Copy
                    (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m)),
            Function.Injective innerProfileRouteRows ∧
              (∀ m,
                Sharpness.RandomCurrent.sources
                  (Sharpness.FluxEdgeCopy.endsM
                    (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m))
                  (innerWitnessRows m) =
                  doubledBoxOriginToInnerEndpointSource n w) ∧
                (∀ m,
                  Sharpness.RandomCurrent.sources
                    (Sharpness.FluxEdgeCopy.endsM
                      (FK.boxGraph 3 (2 * n)) (innerProfileRouteRows m))
                    ((Finset.univ :
                        Finset
                          (Sharpness.FluxEdgeCopy.Copy
                            (FK.boxGraph 3 (2 * n))
                            (innerProfileRouteRows m))) \
                      innerWitnessRows m) =
                    doubledBoxInnerPairSource n v w) ∧
                  ∀ m,
                    ∀ hm : m ∈ rows,
                      doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                          β n v w e0 m ≤
                        ((β / 6) *
                          Sharpness.weight
                            (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
                            (Sharpness.ofEdgeFun
                            (FK.boxGraph 3 (2 * n))
                              (innerProfileRouteRows ⟨m, hm⟩))) /
                          384)

end Exact3D
end StatMech
