module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

def IsingLeapfrogStoppedCouplingBadAtFamily
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :=
  {w : IsingLeapfrogChoiceStringFamily t //
    isingLeapfrogChoiceRun R p w.1 ≠
      isingLeapfrogChoiceRun R p'
        (isingLeapfrogCouplingChoiceTransform t
          (isingLeapfrogBoxInt p) level w).1 /\
      (isingLeapfrogChoiceRun R p w.1 = q \/
        isingLeapfrogChoiceRun R p'
          (isingLeapfrogCouplingChoiceTransform t
            (isingLeapfrogBoxInt p) level w).1 = q)}

end StatMech.Universality
