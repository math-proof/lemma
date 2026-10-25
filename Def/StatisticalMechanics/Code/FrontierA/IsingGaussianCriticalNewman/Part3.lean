/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part2
open Filter Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

def criticalFiniteBoxGlobalParityFourthCumulant (d n : Nat) : Real :=
  ∑ i : sctBox d n,
    finiteParityIntegratedFourthCumulant
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (fun _ => 1) i

end
end StatMech.FrontierA
