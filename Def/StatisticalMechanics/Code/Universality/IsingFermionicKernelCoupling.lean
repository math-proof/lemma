/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogChoiceNext (R : Nat) (p : IsingLeapfrogBox R)
    (b : Bool × Bool) : IsingLeapfrogBox R :=
  if hp : isingLeapfrogBoxBoundary R p then p
  else match b with
    | (false, false) => isingLeapfrogSW R p
    | (true, false) => isingLeapfrogSE R p hp
    | (false, true) => isingLeapfrogNW R p hp
    | (true, true) => isingLeapfrogNE R p hp


def isingLeapfrogChoiceRun (R : Nat) :
    IsingLeapfrogBox R → List (Bool × Bool) → IsingLeapfrogBox R
  | p, [] => p
  | p, b :: bs =>
      isingLeapfrogChoiceRun R (isingLeapfrogChoiceNext R p b) bs


def IsingLeapfrogStoppedChoicePathFamily (R t : Nat)
    (p q : IsingLeapfrogBox R) :=
  {bs : List (Bool × Bool) //
    bs.length = t ∧ isingLeapfrogChoiceRun R p bs = q}

end
end StatMech.Universality
