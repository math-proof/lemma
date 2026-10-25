/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointEscape.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLineFarFifth (m : Nat) (q : IsingLineBox m) : Real :=
  ((m : Real) - (q.1 : Real)) ^ 5

end
end StatMech.Universality
