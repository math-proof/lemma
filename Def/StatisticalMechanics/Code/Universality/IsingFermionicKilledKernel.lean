/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKilledKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part6


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLeapfrogKilledKernel (R t : Nat)
    (p q : IsingLeapfrogBox R) : Real :=
  if isingLeapfrogBoxBoundary R q then 0
  else isingLeapfrogStoppedKernel R t p q


noncomputable def isingLeapfrogExitKernel (R t : Nat)
    (p q : IsingLeapfrogBox R) : Real :=
  if isingLeapfrogBoxBoundary R q then
    isingLeapfrogStoppedKernel R t p q
  else 0

end
end StatMech.Universality
