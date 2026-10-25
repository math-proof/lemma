/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part7


namespace StatMech.Universality

noncomputable def isingLeapfrogKilledPathCount (R : Nat) :
    Nat → IsingLeapfrogBox R → IsingLeapfrogBox R → Nat
  | 0, p, q =>
      if isingLeapfrogBoxBoundary R q then 0 else if p = q then 1 else 0
  | t + 1, p, q =>
      if isingLeapfrogBoxBoundary R q then 0
      else if hp : isingLeapfrogBoxBoundary R p then
        4 * isingLeapfrogKilledPathCount R t p q
      else
        isingLeapfrogKilledPathCount R t (isingLeapfrogSW R p) q +
          isingLeapfrogKilledPathCount R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogKilledPathCount R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogKilledPathCount R t (isingLeapfrogNE R p hp) q


end StatMech.Universality
