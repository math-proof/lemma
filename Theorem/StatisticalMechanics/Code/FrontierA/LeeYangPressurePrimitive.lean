/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.HasPrimitives
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangHalfPlaneDiagonal.Part4
import Def.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive
open Complex Filter Metric Set Topology


namespace StatMech.FrontierA

open StatMech.FK


theorem leeYangRightCayley_mem_ball {z : ℂ} (hz : 0 < z.re) :
    leeYangRightCayley z ∈ ball 0 1 := by
  rw [mem_ball, dist_zero_right, leeYangRightCayley, norm_div, div_lt_one]
  · rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, sub_re, one_re, sub_im, one_im,
      add_re, add_im]
    nlinarith
  · exact norm_pos_iff.mpr (by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith)

theorem leeYangRightCayleyInv_mem {w : ℂ} (hw : w ∈ ball 0 1) :
    0 < (leeYangRightCayleyInv w).re := by
  rw [mem_ball, dist_zero_right] at hw
  rw [leeYangRightCayleyInv, Complex.div_re]
  have hden : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr (by
    intro h
    have hw1 : w = 1 := (sub_eq_zero.mp h).symm
    rw [hw1] at hw
    norm_num at hw)
  have heq :
      (1 + w).re * (1 - w).re / Complex.normSq (1 - w) +
          (1 + w).im * (1 - w).im / Complex.normSq (1 - w) =
        (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
    simp only [add_re, one_re, sub_re, add_im, one_im, sub_im,
      Complex.normSq_apply]
    field_simp
    ring
  rw [heq]
  exact div_pos (by
    rw [sub_pos, Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]) hden

theorem leeYangRightCayleyInv_cayley (z : ℂ) (hz : z ≠ -1) :
    leeYangRightCayleyInv (leeYangRightCayley z) = z := by
  simp only [leeYangRightCayleyInv, leeYangRightCayley]
  have hz1 : z + 1 ≠ 0 := by
    intro h
    apply hz
    calc
      z = (z + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  field_simp [hz1]
  ring

theorem hasDerivAt_leeYangRightCayley (z : ℂ) (hz : 0 < z.re) :
    HasDerivAt leeYangRightCayley (2 / (z + 1) ^ 2) z := by
  have hz1 : z + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have h := ((hasDerivAt_id z).sub (hasDerivAt_const z 1)).div
    ((hasDerivAt_id z).add (hasDerivAt_const z 1)) hz1
  convert h using 1
  simp only [id_eq, Pi.sub_apply, Pi.add_apply, sub_zero, add_zero,
    one_mul, mul_one]
  ring

theorem hasDerivAt_leeYangRightCayleyInv (w : ℂ) (hw : w ∈ ball 0 1) :
    HasDerivAt leeYangRightCayleyInv (2 / (1 - w) ^ 2) w := by
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have hwone : w = 1 := (sub_eq_zero.mp h).symm
    rw [hwone, mem_ball, dist_zero_right] at hw
    norm_num at hw
  have h := ((hasDerivAt_const w 1).add (hasDerivAt_id w)).div
    ((hasDerivAt_const w 1).sub (hasDerivAt_id w)) hw1
  convert h using 1
  simp only [id_eq, Pi.sub_apply, Pi.add_apply, zero_add,
    one_mul]
  ring

end StatMech.FrontierA
