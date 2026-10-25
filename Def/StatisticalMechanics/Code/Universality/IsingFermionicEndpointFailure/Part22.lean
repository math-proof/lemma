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
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part19


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def LineFirstEndpointExtension
    (n N : Nat) (start target : IsingLineBox n) :=
  Sigma fun r : Fin (N + 1) =>
    IsingLineFirstEndpointFamily n r start target ×
      {tail : List Bool // tail.length = N - r}

def lineFirstEndpointExtend
    (n N : Nat) (start target : IsingLineBox n) :
    LineFirstEndpointExtension n N start target ->
      {bs : List Bool // bs.length = N} := fun z =>
  ⟨z.2.1.1 ++ z.2.2.1, by
    rw [List.length_append, z.2.1.2.1, z.2.2.2]
    omega⟩

end
end StatMech.Universality
