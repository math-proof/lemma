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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTwoPointShell
open Finset MeasureTheory Set


namespace StatMech.FrontierA

open Ising Lattice Percolation Sharpness

open StatMech.FrontierB


theorem criticalAxisSite_mem_box {d n : Nat} (hd : 1 ≤ d) :
    criticalAxisSite hd n ∈ box d n := by
  intro i
  by_cases hi : i = (⟨0, hd⟩ : Fin d)
  · simp [criticalAxisSite, hi]
  · simp [criticalAxisSite, hi]

theorem criticalAxisSite_ne_origin {d n : Nat} (hd : 1 ≤ d) (hn : 1 ≤ n) :
    criticalAxisSite hd n ≠ Percolation.origin d := by
  intro h
  have hcoord := congrFun h ⟨0, hd⟩
  simp [criticalAxisSite, Percolation.origin] at hcoord
  omega


theorem criticalAxisTwoPoint_powerLower_of_shellComparison
    {d n : Nat} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hshell : ∀ e ∈ boundaryEdges d (boxSV_boxF d n),
      currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d) e.1 ≤
        currentContinuityFreeTwoPoint d
          (IsingFK.betaC (magnetization d)) (Percolation.origin d)
          (criticalAxisSite (by omega) n)) :
    1 / (4 * d ^ 2 * Real.tanh (IsingFK.betaC (magnetization d)) *
      (2 * (n : Real) + 1) ^ (d - 1)) ≤
      currentContinuityFreeTwoPoint d
        (IsingFK.betaC (magnetization d)) (Percolation.origin d)
        (criticalAxisSite (by omega) n) := by
  let beta := IsingFK.betaC (magnetization d)
  let x := criticalAxisSite (d := d) (by omega : 1 ≤ d) n
  have hbeta : 0 < beta := by
    dsimp [beta]
    rw [isingFK_betaC_eq_tildeBetaCIsing hd]
    exact tildeBetaCIsing_pos hd
  have hxo : x ≠ Percolation.origin d :=
    criticalAxisSite_ne_origin (by omega) hn
  have htarget : 0 ≤ currentContinuityFreeTwoPoint d beta
      (Percolation.origin d) x := by
    rw [currentContinuityFreeTwoPoint_eq_freeInfiniteTwoPoint
      beta hbeta (by omega) (Percolation.origin d) x hxo.symm]
    exact measureReal_nonneg
  have hlower := isingBoxSimonMass_forces_pointwise_powerLower
    d n beta (currentContinuityFreeTwoPoint d beta (Percolation.origin d) x) 1
    (by omega) hn hbeta zero_lt_one htarget
    (phiIsing_ge_one_at_isingFK_betaC hd (boxSV_boxF d n) (by
      change Percolation.origin d ∈ (boxSV_boxF d n : Set (Site d))
      rw [boxSV_coe_boxF]
      exact origin_mem_box' n)) (by
        intro e he
        have heIn : e.1 ∈ box d n := by
          have heFin : e.1 ∈ (boxSV_boxF d n : Set (Site d)) :=
            boundaryEdges_fst_mem he
          rwa [boxSV_coe_boxF] at heFin
        have heNe : e.1 ≠ Percolation.origin d := by
          intro heq
          obtain ⟨_heIn, heOut, heAdj⟩ := shk_mem_boundaryEdges_iff.mp he
          rw [heq] at heAdj
          apply heOut
          change e.2 ∈ (boxSV_boxF d n : Set (Site d))
          rw [boxSV_coe_boxF]
          exact sct_adj_mem_box_of_mem_box_pred hn
            (origin_mem_box' (n - 1)) heAdj
        have hshell' : currentContinuityFreeTwoPoint d beta
            (Percolation.origin d) e.1 ≤
            1 * currentContinuityFreeTwoPoint d beta
              (Percolation.origin d) x := by
          simpa [beta, x] using hshell e he
        exact (corrOriginInner_box_le_currentContinuityFreeTwoPoint
          d n beta hbeta.le e.1 heIn heNe).trans hshell')
  simpa [beta, x] using hlower


end StatMech.FrontierA
