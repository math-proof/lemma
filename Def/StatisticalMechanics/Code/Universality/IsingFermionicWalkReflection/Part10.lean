/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part8


namespace StatMech.Universality

noncomputable def isingLeapfrogStoppedOneStepCount (R : Nat)
    (p q : IsingLeapfrogBox R) : Nat :=
  if hp : isingLeapfrogBoxBoundary R p then
    if p = q then 4 else 0
  else
    (if isingLeapfrogSW R p = q then 1 else 0) +
      (if isingLeapfrogSE R p hp = q then 1 else 0) +
      (if isingLeapfrogNW R p hp = q then 1 else 0) +
      (if isingLeapfrogNE R p hp = q then 1 else 0)

end StatMech.Universality
