/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalNewman.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCollisionDiagonal.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman
open Filter Topology


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

theorem criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling
    (d n : Nat) :
    criticalFiniteBoxNormalizedParityFourthCumulant d n =
      -criticalFiniteBoxFullRenormalizedFourthCoupling d n := by
  unfold criticalFiniteBoxNormalizedParityFourthCumulant
    criticalFiniteBoxFullRenormalizedFourthCoupling
  ring


theorem criticalFiniteBoxNormalizedParityFourthCumulant_tendsto_zero
    (d : Nat) (hd : 4 < d) :
    Tendsto (criticalFiniteBoxNormalizedParityFourthCumulant d)
      atTop (nhds 0) := by
  have h :=
    (criticalFiniteBoxFullRenormalizedFourthCoupling_tendsto_zero d hd).neg
  simpa only [neg_zero,
    ← criticalFiniteBoxNormalizedParityFourthCumulant_eq_neg_coupling] using h

end
end StatMech.FrontierA
