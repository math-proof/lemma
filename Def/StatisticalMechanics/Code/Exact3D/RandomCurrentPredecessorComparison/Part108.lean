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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part115
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

open Classical in
set_option linter.style.longLine false in


def
    ExactSupportOwnerResidualSourcePairEmptyInnerSplitDataFiniteCellCoverRouteShareBoundsAt
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
  ∃ rows : Finset Profile,
    (∀ m : Profile,
      m ∈ Ωactive.filter
          (fun m =>
            doubledBoxOriginIncidentSupport n m = S ∧
              doubledBoxOriginIncidentOwner n m = some ew) →
        m ∈ rows) ∧
      (∃ EmptySplit : Type,
        ∃ emptySplitRows : {m : Profile // m ∈ rows} → Finset EmptySplit,
          ∃ emptyRouteRows :
              (m : {m : Profile // m ∈ rows}) → EmptySplit →
                edgeCopySourcePairData G
                  (doubledBoxOriginToInnerEndpointSource n v)
                  (∅ : Finset (FK.boxVerts 3 (2 * n))),
            Set.InjOn
                (fun p :
                    Sigma (fun _ : {m : Profile // m ∈ rows} => EmptySplit) =>
                  emptyRouteRows p.1 p.2)
                (rows.attach.sigma emptySplitRows) ∧
              ∀ m,
                ∀ hm : m ∈ rows,
                  doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummand
                      β n v w e0 m ≤
                    ∑ i ∈ emptySplitRows ⟨m, hm⟩,
                      ((β / 6) *
                        edgeCopySourcePairDataWeight G β (fun _ => 1)
                          (emptyRouteRows ⟨m, hm⟩ i)) /
                        384) ∧
      (∃ InnerSplit : Type,
        ∃ innerSplitRows : {m : Profile // m ∈ rows} → Finset InnerSplit,
          ∃ innerRouteRows :
              (m : {m : Profile // m ∈ rows}) → InnerSplit →
                edgeCopySourcePairData G
                  (doubledBoxOriginToInnerEndpointSource n w)
                  (doubledBoxInnerPairSource n v w),
            Set.InjOn
                (fun p :
                    Sigma (fun _ : {m : Profile // m ∈ rows} => InnerSplit) =>
                  innerRouteRows p.1 p.2)
                (rows.attach.sigma innerSplitRows) ∧
              ∀ m,
                ∀ hm : m ∈ rows,
                  doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummand
                      β n v w e0 m ≤
                    ∑ i ∈ innerSplitRows ⟨m, hm⟩,
                      ((β / 6) *
                        edgeCopySourcePairDataWeight G β (fun _ => 1)
                          (innerRouteRows ⟨m, hm⟩ i)) /
                        384)

end Exact3D
end StatMech
