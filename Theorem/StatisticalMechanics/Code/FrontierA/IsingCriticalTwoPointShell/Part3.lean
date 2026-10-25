/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTwoPointShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointReduction
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityFreeLeftContinuous
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityMagnetizationFK
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointShell.Part2
open Finset MeasureTheory Set


namespace StatMech.FrontierA

open Ising Lattice Percolation Sharpness

open StatMech.FrontierB


theorem criticalBoundaryTwoPoint_powerLower_of_messagerMiracle
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hMM : CriticalIsingMessagerMiracle d (by omega))
    (x : Site d) (hx : x ∈ boxSV_vbF d n) :
    1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) *
      (2 * ((d * n : Nat) : Real) + 1) ^ (d - 1)) ≤
      currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d) x := by
  have hdn : 1 ≤ d * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)) (Nat.ne_of_gt hn))
  have haxis := criticalAxisTwoPoint_powerLower_of_shellComparison
    hd hdn (hMM (d * n) hdn).1
  exact haxis.trans ((hMM n hn).2 x hx)

end StatMech.FrontierA
