/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part2


namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

def IsingLeapfrogChoiceNoHitAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    (forall k, k <= t ->
      lineFreeEndpoint (isingLeapfrogBoxInt p).1
        ((w.1.map Prod.fst).take k) ≠ level) /\
    (isingLeapfrogChoiceRun R p w.1 = q \/
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 = q)}


def IsingStoppedCouplingSourceFailureAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingSourceFailure R p level w /\
    (isingLeapfrogChoiceRun R p w.1 = q \/
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 = q)}


def IsingStoppedCouplingMirrorFailureAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingMirrorFailure R p p' level w /\
    (isingLeapfrogChoiceRun R p w.1 = q \/
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 = q)}

end StatMech.Universality
