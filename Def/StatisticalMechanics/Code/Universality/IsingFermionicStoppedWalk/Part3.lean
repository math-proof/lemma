/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLeapfrogStoppedMean (R t : Nat)
    (f : IsingLeapfrogBox R → Complex) (p : IsingLeapfrogBox R) : Complex :=
  ∑ q, (isingLeapfrogStoppedKernel R t p q : Complex) * f q

end
end StatMech.Universality
