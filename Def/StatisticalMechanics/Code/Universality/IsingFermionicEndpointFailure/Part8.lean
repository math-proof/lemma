module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointEscape.Part4
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicOrderedEndpointConvolution
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTailEndpointRace
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointFailure.Part7


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

def IsingMirrorFailureOutputAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingStoppedCouplingMirrorFailureFamily R t p p' level //
    isingLeapfrogChoiceRun R p'
      (isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) level w.1).1 = q}

end
end StatMech.Universality
