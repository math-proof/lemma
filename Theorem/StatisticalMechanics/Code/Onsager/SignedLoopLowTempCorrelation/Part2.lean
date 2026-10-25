/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempCorrelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierDuality.Part4
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Walls.kwd_crosscountparity.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopLowTempCorrelation.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem isingExpectation_twoPoint_eq_lowTempPathRatio
    (beta : Real) {u v : V} (path : G.Walk u v) :
    isingExpectation G beta 0
        (fun config => spin config u * spin config v) =
      ons_lowTempPathNumerator G beta path /
        ons_lowTempContourDenominator G beta := by
  let prefactor := Real.exp (beta * G.edgeFinset.card)
  have hprefactor : prefactor ≠ 0 := (Real.exp_pos _).ne'
  have hnum :
      (∑ config : ConfigSpace V,
        isingWeight G beta 0 config *
          (spin config u * spin config v)) =
        prefactor * ons_lowTempPathNumerator G beta path := by
    unfold ons_lowTempPathNumerator
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro config _
    rw [isingWeight_eq_lowTempCutWeight,
      ← ons_lowTempPathSign_eq_spin_mul G config path]
    simp only [prefactor]
    ring
  have hden : isingZ G beta 0 =
      prefactor * ons_lowTempContourDenominator G beta := by
    rw [isingZ_low_temp_expansion]
    rfl
  unfold isingExpectation isingProb
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, hnum, hden]
  field_simp [hprefactor]

end StatMech.Onsager
