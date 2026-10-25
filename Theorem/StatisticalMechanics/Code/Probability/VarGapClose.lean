/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/VarGapClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.BKKKLLevel2Prove.Part2
open scoped BigOperators
open Finset
open Real Set

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem vgc_totalInfl_zero_of_maxInfl_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
    totalInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  unfold totalInfl
  apply Finset.sum_eq_zero
  intro e _
  have hle : OSSS.infl (OSSS.bernoulliWeight p) f e
      ≤ maxInfl (OSSS.bernoulliWeight p) f := kkl_infl_le_maxInfl _ f e
  have hge : 0 ≤ OSSS.infl (OSSS.bernoulliWeight p) f e :=
    kkl_infl_nonneg (OSSS.bernoulliWeight_isProbWeight hp0.le hp1.le) f e
  rw [hδ0] at hle
  linarith


theorem vgc_var_zero_of_maxInfl_zero [Nonempty ι] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (φ : ConfigSpace ι → Bool)
    (hδ0 : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) = 0) :
    OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      * (1 - OSSS.expect (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)) = 0 := by
  set f := fun ω : ConfigSpace ι => if φ ω then (1 : ℝ) else 0 with hf
  set μ := OSSS.expect (OSSS.bernoulliWeight p) f with hμ
  have hpoin := bkt2p_poincare_half hp0 hp1 φ
  rw [← hμ] at hpoin
  have hT0 := vgc_totalInfl_zero_of_maxInfl_zero hp0 hp1 φ hδ0
  rw [hT0, mul_zero] at hpoin
  
  have hvarF := ptn_var_eq_fourierWeight hp0 hp1 f
  have hvar_eq : OSSS.var (OSSS.bernoulliWeight p) f = μ * (1 - μ) := by
    rw [mil_var_eq φ, ← hμ]; ring
  have hvar_nn : 0 ≤ μ * (1 - μ) := by
    rw [← hvar_eq, hvarF]
    exact Finset.sum_nonneg (fun S _ => sq_nonneg _)
  linarith


end StatMech.Probability
