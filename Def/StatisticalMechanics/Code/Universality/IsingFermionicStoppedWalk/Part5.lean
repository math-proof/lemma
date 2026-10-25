/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part3


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLeapfrogStoppedKernelGradientSq
    (R t : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogStoppedKernel R t p q -
    isingLeapfrogStoppedKernel R t p' q) ^ 2


noncomputable def isingLeapfrogStoppedKernelTimeGradientSq
    (R t t' : Nat) (p p' : IsingLeapfrogBox R) : Real :=
  ∑ q, (isingLeapfrogStoppedKernel R t p q -
    isingLeapfrogStoppedKernel R t' p' q) ^ 2

end
end StatMech.Universality
