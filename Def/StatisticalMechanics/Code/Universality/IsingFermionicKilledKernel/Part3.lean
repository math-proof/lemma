/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part2


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLeapfrogKilledKernelTimeGradientSq
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogKilledKernel R t p q -
    isingLeapfrogKilledKernel R t' p' q) ^ 2


noncomputable def isingLeapfrogExitKernelTimeGradientSq
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogExitKernel R t p q -
    isingLeapfrogExitKernel R t' p' q) ^ 2

end
end StatMech.Universality
