/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCollisionDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part4
open Filter Finset Set Topology
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


section CriticalFiniteBox

def criticalFiniteBoxParityIntegratedFourthCumulant (d n : Nat) : Real :=
  finiteParityIntegratedFourthCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1)
    (criticalFiniteBoxOrigin d n)


def criticalFiniteBoxFullRenormalizedFourthCoupling (d n : Nat) : Real :=
  -criticalFiniteBoxParityIntegratedFourthCumulant d n /
    (2 * criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)

end CriticalFiniteBox
end
end StatMech.FrontierA
