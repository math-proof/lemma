/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part2


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

theorem firstVerticalBoundaryTimeEndpointFailure_eq
    (R : Nat) (start : Int) (ys : List Bool) (j : Nat)
    (hj : j <= ys.length)
    (hboundary : lineFreeEndpoint start (ys.take j) = 0 \/
      lineFreeEndpoint start (ys.take j) = R)
    (hminimal : forall l, l < j ->
      lineFreeEndpoint start (ys.take l) ≠ 0 /\
        lineFreeEndpoint start (ys.take l) ≠ R) :
    firstVerticalBoundaryTimeEndpointFailure R start ys = j := by
  classical
  let hex : exists k, verticalBoundaryAtEndpointFailure R start ys k :=
    ⟨j, hj, hboundary⟩
  unfold firstVerticalBoundaryTimeEndpointFailure
  rw [dif_pos hex]
  apply Nat.le_antisymm
  · exact Nat.find_min' hex ⟨hj, hboundary⟩
  · by_contra hnot
    have hlt : Nat.find hex < j := by omega
    have hspec := Nat.find_spec hex
    rcases hspec.2 with hzero | hR
    · exact (hminimal (Nat.find hex) hlt).1 hzero
    · exact (hminimal (Nat.find hex) hlt).2 hR


end
end StatMech.Universality
