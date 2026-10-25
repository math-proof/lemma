/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part2


namespace StatMech.Universality

open Finset

noncomputable section

theorem isingLeapfrogStoppedKernel_succ (R t : Nat)
    (p q : IsingLeapfrogBox R) :
    isingLeapfrogStoppedKernel R (t + 1) p q =
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedKernel R t p q
      else
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p hp) q) / 4 := by
  rfl


end
end StatMech.Universality
