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
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part111
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictSectorYFilterSwitchedSourceSectorResidualMomentActiveOriginIncidentSupportPatternOwnerEdgeResidualBranchSixthFiniteSumBoundsAt
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
                (∑ S ∈ supportPatterns,
                  ∑ m ∈ Ωactive.filter
                      (fun m => doubledBoxOriginIncidentSupport n m = S),
                    match doubledBoxOriginIncidentOwner n m with
                    | none => 0
                    | some ew =>
                        doubledBoxSwitchedSourceSectorResidualMomentEmptyBranchSummandAtEdge
                          β n v w e0 ew m) ≤
                    (β * doubledBoxOriginToInnerEndpointSourcePairEmptySum
                      β n v) /
                      6 ∧
                  (∑ S ∈ supportPatterns,
                    ∑ m ∈ Ωactive.filter
                        (fun m => doubledBoxOriginIncidentSupport n m = S),
                      match doubledBoxOriginIncidentOwner n m with
                      | none => 0
                      | some ew =>
                          doubledBoxSwitchedSourceSectorResidualMomentInnerPairBranchSummandAtEdge
                            β n v w e0 ew m) ≤
                      (β *
                        Sharpness.sourcePairSum (FK.boxGraph 3 (2 * n)) β
                          (fun _ => 1)
                          (doubledBoxOriginToInnerEndpointSource n w)
                          (doubledBoxInnerPairSource n v w)) /
                        6

end Exact3D
end StatMech
