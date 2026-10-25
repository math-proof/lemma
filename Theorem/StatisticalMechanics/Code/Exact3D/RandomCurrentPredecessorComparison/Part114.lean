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
import Def.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part106
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    exactSupportOwnerResidualSourcePairRouteShareBoundsAt_of_profileWitnessRouteShareBoundsAt
    {β : ℝ} {n : ℕ}
    (hprofile :
      ExactSupportOwnerResidualSourcePairProfileWitnessRouteShareBoundsAt
        β n) :
    ExactSupportOwnerResidualSourcePairRouteShareBoundsAt β n := by
  intro v hvwedge hlt hypos
  classical
  dsimp only at hprofile ⊢
  intro e0 hedge Ω
  let w := boxVertStrictSectorYPredecessor3 v hvwedge hlt hypos
  let Edge := ↥(FK.boxGraph 3 (2 * n)).edgeFinset
  let Profile := Edge → ℕ
  let Ωactive : Finset Profile :=
    Ω.filter (doubledBoxIncrementedFullSourceActive n w e0)
  let supportPatterns : Finset (Finset Edge) :=
    Finset.filter (fun S => S.Nonempty)
      (Finset.powerset (doubledBoxOriginIncidentEdges n))
  rcases hprofile v hvwedge hlt hypos e0 hedge Ω with
    ⟨hemptyProfile, hinnerProfile⟩
  constructor
  · intro S hS ew hew
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    rcases hemptyProfile S (by simpa [supportPatterns] using hS) ew hew with
      ⟨profileRoute, witness, hinjProfile, hwitness, hpointProfile⟩
    let route : Profile →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n v)
          (∅ : Finset (FK.boxVerts 3 (2 * n))) :=
      fun m => edgeCopySourcePairData_of_witness (FK.boxGraph 3 (2 * n))
        (hwitness m)
    refine ⟨route, ?_, ?_⟩
    · simpa [route, cell, Ωactive, w] using
        edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
          (G := FK.boxGraph 3 (2 * n)) (s := cell)
          witness hwitness
          (by simpa [cell, Ωactive, w] using hinjProfile)
    · intro m hm
      simpa [route] using
        hpointProfile m (by simpa [cell, Ωactive, w] using hm)
  · intro S hS ew hew
    let cell : Finset Profile :=
      Ωactive.filter
        (fun m =>
          doubledBoxOriginIncidentSupport n m = S ∧
            doubledBoxOriginIncidentOwner n m = some ew)
    rcases hinnerProfile S (by simpa [supportPatterns] using hS) ew hew with
      ⟨profileRoute, witness, hinjProfile, hwitness, hpointProfile⟩
    let route : Profile →
        edgeCopySourcePairData (FK.boxGraph 3 (2 * n))
          (doubledBoxOriginToInnerEndpointSource n w)
          (doubledBoxInnerPairSource n v w) :=
      fun m => edgeCopySourcePairData_of_witness (FK.boxGraph 3 (2 * n))
        (hwitness m)
    refine ⟨route, ?_, ?_⟩
    · simpa [route, cell, Ωactive, w] using
        edgeCopySourcePairData_of_witness_route_injOn_of_profileRoute_injOn
          (G := FK.boxGraph 3 (2 * n)) (s := cell)
          witness hwitness
          (by simpa [cell, Ωactive, w] using hinjProfile)
    · intro m hm
      simpa [route] using
        hpointProfile m (by simpa [cell, Ωactive, w] using hm)

end Exact3D
end StatMech
