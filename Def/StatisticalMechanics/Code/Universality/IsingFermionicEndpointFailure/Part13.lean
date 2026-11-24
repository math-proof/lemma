module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
public import Instance.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointFailure.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingLineFirstEndpointFamily
    (n k : Nat) (start target : IsingLineBox n) :=
  {ys : List Bool // ys.length = k /\
    isingLineChoiceRun n start ys = target /\
    forall l, l < k -> ¬ isingLineBoxBoundary n
      (isingLineChoiceRun n start (ys.take l))}

end
end StatMech.Universality
