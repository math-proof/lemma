module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRace.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicTailEndpointRace.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset

noncomputable section

abbrev IsingEndpointRaceTail (t : Nat) (j : Fin (t + 1)) :=
  {tail : List (Bool × Bool) // tail.length = t - j}


end
end StatMech.Universality
