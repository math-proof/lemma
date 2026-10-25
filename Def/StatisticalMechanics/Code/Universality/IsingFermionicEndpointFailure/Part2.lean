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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def verticalBoundaryAtEndpointFailure
    (R : Nat) (start : Int) (ys : List Bool) (j : Nat) : Prop :=
  j <= ys.length /\
    (lineFreeEndpoint start (ys.take j) = 0 \/
      lineFreeEndpoint start (ys.take j) = R)

noncomputable def firstVerticalBoundaryTimeEndpointFailure
    (R : Nat) (start : Int) (ys : List Bool) : Nat := by
  classical
  exact if h : exists j, verticalBoundaryAtEndpointFailure R start ys j then
      Nat.find h
    else ys.length

end
end StatMech.Universality
