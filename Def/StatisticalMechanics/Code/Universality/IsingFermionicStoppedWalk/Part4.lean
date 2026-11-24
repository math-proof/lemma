module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLeapfrogStoppedBoundaryMass (R t : Nat)
    (p : IsingLeapfrogBox R) : Real :=
  ∑ q with isingLeapfrogBoxBoundary R q,
    isingLeapfrogStoppedKernel R t p q

end
end StatMech.Universality
