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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part13


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingOrderedFarEndpointFamily
    (m n t : Nat) (start target : IsingLineBox n)
    (markX targetX : Int) :=
  Sigma fun k : Fin (t + 1) =>
    Sigma fun j : Fin k =>
      IsingLineFarFirstBoundaryFamily m j ×
        IsingLineFirstEndpointFamily n k start target ×
        VerticalChoicePathFamily (k - j) markX targetX ×
        {tail : List (Bool × Bool) // tail.length = t - k}

end
end StatMech.Universality
