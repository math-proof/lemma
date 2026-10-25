/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000


namespace StatMech

namespace Sharpness

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem magnetization_zero_field (β : ℝ) (o : V) :
    isingExpectation G β 0 (fun s => spin s o) = 0 := by
  unfold isingExpectation
  have key : ∀ s, isingProb G β 0 (flipCfg s) * spin (flipCfg s) o
      = - (isingProb G β 0 s * spin s o) := by
    intro s
    have hsp : spin (flipCfg s) o = - spin s o := spin_flipCfg s o
    have hprob : isingProb G β 0 (flipCfg s) = isingProb G β 0 s := by
      unfold isingProb isingWeight hamiltonian
      congr 2
      simp only [zero_mul, sub_zero]
      congr 2
      exact Finset.sum_congr rfl (fun e _ => bond_flipCfg s e)
    rw [hsp, hprob]; ring
  have hS : (∑ s : ConfigSpace V, isingProb G β 0 s * spin s o)
      = ∑ s : ConfigSpace V, isingProb G β 0 (flipCfg s) * spin (flipCfg s) o :=
    (Equiv.sum_comp (flipEquiv (V := V)) (fun s => isingProb G β 0 s * spin s o)).symm
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_neg_distrib] at hS
  linarith


theorem ghs_susceptibility_bound (β h : ℝ) (hh : 0 < h) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
        ≤ isingExpectation G β h (fun s => spin s o) / h
      ∧ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 1 / h := by
  set φ : ℝ → ℝ := fun h => isingExpectation G β h (fun s => spin s o) with hφ
  have hdiff : DifferentiableAt ℝ φ h := (hasDerivAt_magnetization G β h o).differentiableAt
  have hphi0 : φ 0 = 0 := magnetization_zero_field G β o
  
  have hslope := hconc.deriv_le_slope (x := 0) (y := h)
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr hh.le) hh hdiff
  rw [slope_def_field, hphi0, sub_zero, sub_zero] at hslope
  refine ⟨hslope, ?_⟩
  
  have hle1 : φ h ≤ 1 := expectation_spin_le_one G β h o
  have hdivle : φ h / h ≤ 1 / h := (div_le_div_iff_of_pos_right hh).mpr hle1
  exact hslope.trans hdivle

end Sharpness
end StatMech
