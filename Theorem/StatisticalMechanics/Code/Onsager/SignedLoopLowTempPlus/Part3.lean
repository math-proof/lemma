/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempPlus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
import Theorem.StatisticalMechanics.Code.Ising.FVConsistencyProve.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempPlus.Part3
open scoped BigOperators
open Finset SimpleGraph MeasureTheory


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice StatMech.Walls


theorem integral_plusMeasure_twoPoint_eq_lowTempPathRatio
    (d n : Nat) (beta : Real) {u v : Site d}
    (path : (hypercubicLattice d).Walk u v) :
    (∫ config, spin config u * spin config v
        ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
      ons_plusLowTempPathNumerator d n beta path /
        ons_plusLowTempContourDenominator d n beta := by
  let prefactor : Real := Real.exp (beta * (bondFinsetTouch d n).card)
  have hprefactor : prefactor ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ tau : {x // x ∈ box d n} → Bool,
        fvWeight (plusField d) n (bondFinsetTouch d n) beta 0 tau *
          (spin (glue (plusField d) tau) u *
            spin (glue (plusField d) tau) v)) =
        prefactor * ons_plusLowTempPathNumerator d n beta path := by
    unfold ons_plusLowTempPathNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau _
    rw [fvWeight_zero_eq_lowTempCutWeight,
      ← ons_plusLowTempPathSign_eq_spin_mul (glue (plusField d) tau) path]
    simp only [prefactor]
    ring
  have hden :
      fvZ (plusField d) n (bondFinsetTouch d n) beta 0 =
        prefactor * ons_plusLowTempContourDenominator d n beta := by
    unfold fvZ ons_plusLowTempContourDenominator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tau _
    rw [fvWeight_zero_eq_lowTempCutWeight]
  rw [plusMeasure_coe,
    integral_fvMeasure_eq_sum (plusField d) n
      (bondFinsetTouch d n) beta 0]
  unfold fvProb
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hnum, hden]
  field_simp [hprefactor]

end StatMech.Onsager
