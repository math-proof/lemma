/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part4
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


section CriticalFiniteBox

def criticalFiniteBoxOrigin (d n : Nat) : sctBox d n :=
  ⟨Percolation.origin d, origin_mem_box' n⟩


def criticalFiniteBoxRenormalizedFourthCoupling (d n : Nat) : Real :=
  -finiteDistinctIntegratedFourthCumulant
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
      (criticalFiniteBoxOrigin d n) /
    (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)


end CriticalFiniteBox
end
end StatMech.FrontierA
