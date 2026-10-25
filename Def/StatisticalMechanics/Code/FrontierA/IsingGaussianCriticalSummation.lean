/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


def criticalFreeBoxSusceptibility (d R : Nat) : Real :=
  ∑ x ∈ boxSV_boxF d R,
    currentContinuityFreePairKernel d (IsingFK.betaC (magnetization d)) x

end
end StatMech.FrontierA
