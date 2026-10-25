/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PlusStateTIClose.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part4
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.ConfigSpace

open StatMech.FK

variable {d : ℕ}


noncomputable def iti_decaySet (β h : ℝ) (g : Multiplicative (Site d)) (φ : ℕ → ℕ) :
    Submodule ℝ C(ConfigSpace (Site d), ℝ) where
  carrier := {hh | Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g
      (BoundedContinuousFunction.mkOfCompact hh)) atTop (𝓝 0)}
  add_mem' {hh hh'} h1 h2 := by
    simp only [Set.mem_setOf_eq] at h1 h2 ⊢
    have hsum := h1.add h2; rw [add_zero] at hsum
    refine hsum.congr (fun n => ?_)
    rw [BoundedContinuousFunction.mkOfCompact_add, iti_decayFun_add]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    have hz : pstc_decayFun (fun n => plusMeasure d (φ n) β h) g
        (BoundedContinuousFunction.mkOfCompact (0 : C(ConfigSpace (Site d), ℝ)))
      = fun _ => (0:ℝ) := by
      funext n; rw [BoundedContinuousFunction.mkOfCompact_zero, iti_decayFun_zero]
    rw [hz]; exact tendsto_const_nhds
  smul_mem' c hh h1 := by
    simp only [Set.mem_setOf_eq] at h1 ⊢
    have hsmul := h1.const_mul c; rw [mul_zero] at hsmul
    refine hsmul.congr (fun n => ?_)
    have hms : BoundedContinuousFunction.mkOfCompact (c • hh)
        = c • BoundedContinuousFunction.mkOfCompact hh := rfl
    rw [hms, iti_decayFun_smul]


end Ising
end StatMech
