/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part8


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingStoppedCouplingSourceFailure
    (R : Nat) (p : IsingLeapfrogBox R) (level : Int)
    {t : Nat} (w : IsingLeapfrogChoiceStringFamily t) : Prop :=
  ∃ split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level,
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = some split ∧
    ¬ IsingLeapfrogChoiceExecValid R p
      (w.1.take split.before.length)


def IsingStoppedCouplingSourceFailureFamily
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingSourceFailure R p level w}

def IsingStoppedCouplingMirrorFailure
    (R : Nat) (p p' : IsingLeapfrogBox R) (level : Int)
    {t : Nat} (w : IsingLeapfrogChoiceStringFamily t) : Prop :=
  ∃ split : IsingDiagonalWalkHitSplit (isingLeapfrogBoxInt p) level,
    isingDiagonalWalkFirstHitSplit? (isingLeapfrogBoxInt p) level
      (isingLeapfrogChoiceSteps w.1) = some split ∧
    ¬ IsingLeapfrogChoiceExecValid R p'
      ((isingLeapfrogCouplingChoiceTransform t
        (isingLeapfrogBoxInt p) level w).1.take split.before.length)


def IsingStoppedCouplingMirrorFailureFamily
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    IsingStoppedCouplingMirrorFailure R p p' level w}

end
end StatMech.Universality
