/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Integration.Part2
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Def.StatisticalMechanics.Code.OSSS.LogCesaroLimit
open scoped BigOperators
open Filter Topology Real Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

namespace LogCesaroLimit

open BetaThresholdBound


lemma harmonicReal_eq (n : ℕ) : harmonicReal n = (harmonic n : ℝ) := by
  rw [harmonicReal, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  · intro i _
    rw [one_div]


theorem harmonicReal_div_log_tendsto_one :
    Tendsto (fun n => harmonicReal n / Real.log (n : ℝ)) atTop (nhds 1) := by
  have hdiff : Tendsto (fun n : ℕ => harmonicReal n - Real.log (n : ℝ)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa only [harmonicReal_eq] using tendsto_harmonic_sub_log
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hzero : Tendsto
      (fun n : ℕ => (harmonicReal n - Real.log (n : ℝ)) / Real.log (n : ℝ))
      atTop (nhds 0) := hdiff.div_atTop hlog
  have hadd : Tendsto
      (fun n : ℕ => (harmonicReal n - Real.log (n : ℝ)) / Real.log (n : ℝ) + 1)
      atTop (nhds 1) := by
    simpa using hzero.add_const 1
  refine hadd.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
  field_simp
  ring


end LogCesaroLimit
end OSSS
end StatMech
