/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Def.StatisticalMechanics.Code.Probability.BonamiTensorize.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem bnt_vectorTwoPoint_zero : bnt_VectorTwoPoint 0 := by
  intro n u v
  have hq : (1 : ℝ) + 0 ^ 2 = 1 := by norm_num
  rw [hq, show (2 : ℝ) / 1 = 2 by norm_num, Real.rpow_two]
  have e1 : (fun ω : Fin n → Bool => (1 + (0 : ℝ)) / 2 * u ω + (1 - 0) / 2 * v ω)
          = (fun ω => (1 / 2) * u ω + (1 / 2) * v ω) := by funext ω; norm_num
  have e2 : (fun ω : Fin n → Bool => (1 - (0 : ℝ)) / 2 * u ω + (1 + 0) / 2 * v ω)
          = (fun ω => (1 / 2) * u ω + (1 / 2) * v ω) := by funext ω; norm_num
  rw [e1, e2]
  set m := (fun ω : Fin n → Bool => (1 / 2 : ℝ) * u ω + (1 / 2) * v ω) with hm
  rw [show (bnt_qnormPow 2 m + bnt_qnormPow 2 m) / 2 = bnt_qnormPow 2 m by ring]
  rw [Real.rpow_one, Real.rpow_one]
  have htri : bnt_qnorm 2 m ≤ (bnt_qnorm 2 u + bnt_qnorm 2 v) / 2 := by
    have hmink := bnt_qnorm_add_le (n := n) (p := 2) (by norm_num)
      (fun ω => (1 / 2 : ℝ) * u ω) (fun ω => (1 / 2 : ℝ) * v ω)
    have hh1 := bnt_qnorm_const_mul (n := n) (p := 2) (by norm_num) (1 / 2 : ℝ) u
    have hh2 := bnt_qnorm_const_mul (n := n) (p := 2) (by norm_num) (1 / 2 : ℝ) v
    rw [hm]
    rw [hh1, hh2] at hmink
    simp only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hmink
    calc bnt_qnorm 2 (fun ω => (1 / 2 : ℝ) * u ω + (1 / 2 : ℝ) * v ω)
        ≤ 1 / 2 * bnt_qnorm 2 u + 1 / 2 * bnt_qnorm 2 v := hmink
      _ = (bnt_qnorm 2 u + bnt_qnorm 2 v) / 2 := by ring
  have hmnn : 0 ≤ bnt_qnorm 2 m := bnt_qnorm_nonneg 2 m
  have hrhs_nn : 0 ≤ (bnt_qnorm 2 u + bnt_qnorm 2 v) / 2 := by
    have := bnt_qnorm_nonneg 2 u; have := bnt_qnorm_nonneg 2 v; linarith
  have hsq : bnt_qnorm 2 m ^ 2 ≤ ((bnt_qnorm 2 u + bnt_qnorm 2 v) / 2) ^ 2 := by
    nlinarith [htri, hmnn, hrhs_nn]
  have hmpow : bnt_qnorm 2 m ^ (2 : ℝ) = bnt_qnormPow 2 m :=
    bnt_qnorm_rpow_self (by norm_num) m
  rw [Real.rpow_two] at hmpow
  rw [← hmpow]; exact hsq


theorem bnt_vectorTwoPoint_one : bnt_VectorTwoPoint 1 := by
  intro n u v
  have hq : (1 : ℝ) + 1 ^ 2 = 2 := by norm_num
  rw [hq, show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have e1 : (fun ω : Fin n → Bool => (1 + (1 : ℝ)) / 2 * u ω + (1 - 1) / 2 * v ω) = u := by
    funext ω; norm_num
  have e2 : (fun ω : Fin n → Bool => (1 - (1 : ℝ)) / 2 * u ω + (1 + 1) / 2 * v ω) = v := by
    funext ω; norm_num
  rw [e1, e2]
  have hu : bnt_qnorm 2 u ^ (2 : ℝ) = bnt_qnormPow 2 u := bnt_qnorm_rpow_self (by norm_num) u
  have hv : bnt_qnorm 2 v ^ (2 : ℝ) = bnt_qnormPow 2 v := bnt_qnorm_rpow_self (by norm_num) v
  rw [hu, hv]


end Probability
end StatMech
