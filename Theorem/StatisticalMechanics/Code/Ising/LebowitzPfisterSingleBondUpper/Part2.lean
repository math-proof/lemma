/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSingleBondUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterSingleBondUpper
open Set


namespace StatMech.Ising

noncomputable section

theorem singleBondInterfaceFreeEnergy_le
    {K m1 m2 : Real} (hK : 0 <= K)
    (hm10 : 0 <= m1) (hm11 : m1 <= 1)
    (hm20 : 0 <= m2) (hm21 : m2 <= 1) :
    singleBondInterfaceFreeEnergy K m1 m2 <= 2 * K * (m1 * m2) := by
  let a := m1 * m2
  have ha0 : 0 <= a := mul_nonneg hm10 hm20
  have ha1 : a <= 1 := mul_le_one₀ hm11 hm20 hm21
  have ht0 : 0 <= Real.tanh K := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.mpr hK) (Real.cosh_pos K).le
  have ht1 : Real.tanh K < 1 := Real.tanh_lt_one K
  have hat : a * Real.tanh K ∈ Set.Icc (-1 : Real) 1 := by
    constructor
    · exact (mul_nonneg ha0 ht0).trans' (by norm_num)
    · exact (mul_le_of_le_one_left ht0 ha1).trans ht1.le
  have hart := artanh_mul_tanh_le_mul ha0 ha1 hK
  rw [Real.artanh_eq_half_log hat] at hart
  unfold singleBondInterfaceFreeEnergy
  change Real.log ((1 + a * Real.tanh K) / (1 - a * Real.tanh K)) <=
    2 * K * a
  nlinarith

end
end StatMech.Ising
