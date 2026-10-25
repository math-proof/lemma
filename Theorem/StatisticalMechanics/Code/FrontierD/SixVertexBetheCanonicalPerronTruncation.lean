/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheLogNumerator_lower
    {c : Real} (hc : 2 < c) (x : Real) :
    (c ^ 2 - 2) ^ 2 <= sixVertexBetheLogNumerator c x := by
  unfold sixVertexBetheLogNumerator
  have hcos := Real.neg_one_le_cos x
  have ha : 0 < c ^ 2 - 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcos ha.le]

theorem sixVertexBetheLogNumerator_pos
    {c : Real} (hc : 2 < c) (x : Real) :
    0 < sixVertexBetheLogNumerator c x := by
  have h := sixVertexBetheLogNumerator_lower hc x
  have hc2 : 0 < c ^ 2 - 2 := by
    have hcplus : 0 < c + 2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hc) hcplus]
  have hsquare : 0 < (c ^ 2 - 2) ^ 2 := by
    exact pow_pos hc2 2
  linarith

theorem sixVertexBetheLogDenominator_nonneg (x : Real) :
    0 <= sixVertexBetheLogDenominator x := by
  unfold sixVertexBetheLogDenominator
  linarith [Real.cos_le_one x]

theorem abs_log_sub_log_le_of_lower
    {m x y : Real} (hm : 0 < m) (hx : m <= x) (hy : m <= y) :
    |Real.log x - Real.log y| <= |x - y| / m := by
  have hxpos : 0 < x := hm.trans_le hx
  have hypos : 0 < y := hm.trans_le hy
  have hforward {u v : Real} (hu : m <= u) (huPos : 0 < u)
      (hvPos : 0 < v) (huv : u <= v) :
      Real.log v - Real.log u <= (v - u) / m := by
    calc
      Real.log v - Real.log u = Real.log (v / u) := by
        rw [Real.log_div hvPos.ne' huPos.ne']
      _ <= v / u - 1 := Real.log_le_sub_one_of_pos (div_pos hvPos huPos)
      _ = (v - u) / u := by field_simp [huPos.ne']
      _ <= (v - u) / m := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hm hu
  rcases le_total x y with hxy | hyx
  · have hlog := hforward hx hxpos hypos hxy
    rw [abs_of_nonpos (sub_nonpos.mpr
      (Real.log_le_log hxpos hxy)), abs_of_nonpos (sub_nonpos.mpr hxy)]
    convert hlog using 1 <;> ring
  · have hlog := hforward hy hypos hxpos hyx
    rw [abs_of_nonneg (sub_nonneg.mpr
      (Real.log_le_log hypos hyx)), abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact hlog

theorem abs_sixVertexBetheLogNumerator_sub_le
    {c : Real} (hc : 2 < c) (x y : Real) :
    |sixVertexBetheLogNumerator c x -
        sixVertexBetheLogNumerator c y| <=
      (2 * (c ^ 2 - 1)) * |x - y| := by
  unfold sixVertexBetheLogNumerator
  rw [show
    (c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos x -
        ((c ^ 2 - 1) ^ 2 + 1 + 2 * (c ^ 2 - 1) * Real.cos y) =
      (2 * (c ^ 2 - 1)) * (Real.cos x - Real.cos y) by ring,
    abs_mul, abs_of_pos (by nlinarith : 0 < 2 * (c ^ 2 - 1))]
  exact mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x y)
    (by nlinarith [sq_nonneg c])

theorem abs_sixVertexBetheLogDenominator_sub_le (x y : Real) :
    |sixVertexBetheLogDenominator x -
        sixVertexBetheLogDenominator y| <= 2 * |x - y| := by
  unfold sixVertexBetheLogDenominator
  rw [show (2 - 2 * Real.cos x) - (2 - 2 * Real.cos y) =
      -2 * (Real.cos x - Real.cos y) by ring,
    abs_mul]
  norm_num
  exact Real.abs_cos_sub_cos_le x y


end
end StatMech.FrontierD
