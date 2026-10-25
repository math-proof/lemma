/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareBoundaryCancellation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareFaceLaplacian.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryGeometry
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryCancellation.Part3


namespace StatMech.Universality

open Complex SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def FKIsingSquarePerimeterGlobalPathSwitchingAt.toCancellationSwitching
    {n : Nat} {hn : 0 < n} {side : FKIsingSquareBoundarySide}
    {k : Fin (2 * n)}
    (S : FKIsingSquarePerimeterGlobalPathSwitchingAt n hn side k) :
    FKIsingSquarePerimeterCancellationSwitchingAt n hn side k where
  uncut := S.uncut
  pairing := S.pairing
  paired_summand := by
    intro omega
    let D := fkIsingSquareWiredDobrushinDomain n hn
    let z : FKIsingSquareWiredCarrier n :=
      .dart (fkIsingSquarePerimeterEdge n side k,
        fkIsingSquarePerimeterCancelledSide side)
    change D.fermionicSummand (S.pairing omega) z =
      -D.fermionicSummand omega z
    unfold FKIsingDobrushinDomain.fermionicSummand
    by_cases hz : z ∈ D.exploration omega
    · have hz' : z ∈ D.exploration (S.pairing omega) :=
        (S.visited omega).2 hz
      rw [if_pos hz', if_pos hz, S.mass omega, S.phase omega hz]
      ring
    · have hz' : z ∉ D.exploration (S.pairing omega) := by
        exact fun h ↦ hz ((S.visited omega).1 h)
      rw [if_neg hz', if_neg hz, neg_zero]

end
end StatMech.Universality
