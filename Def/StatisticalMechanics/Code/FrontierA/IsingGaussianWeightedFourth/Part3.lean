/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth.Part3
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

section CriticalBox

def criticalFiniteBoxWeightedParityFourthCumulant
    (d n : Nat) (a : sctBox d n -> Real) : Real :=
  finiteWeightedParityFourthCumulant
    (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) a


def criticalFiniteBoxWeightedNormalizedFourthCumulant
    (d n : Nat) (a : sctBox d n -> Real) : Real :=
  criticalFiniteBoxWeightedParityFourthCumulant d n a /
    (2 * (Fintype.card (sctBox d n) : Real) *
      criticalFreeBoxSusceptibility d (2 * n) ^ 2 *
      ((2 * n + 1 : Nat) : Real) ^ d)

end CriticalBox
end
end StatMech.FrontierA
