/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFiniteRoots.Part2
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem tendsto_sixVertexThetaQuadraticDenominator :
    Tendsto (fun c : Real => c ^ 2 - 4) atTop atTop := by
  have hsq : Tendsto (fun c : Real => c * c) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (max 1 b)] with c hc
    have hc1 : 1 <= c := le_trans (le_max_left _ _) hc
    have hcb : b <= c := le_trans (le_max_right _ _) hc
    nlinarith
  simpa only [pow_two, sub_eq_add_neg] using
    (tendsto_atTop_add_const_right atTop (-4) hsq)

theorem sixVertexTheta_ratio_abs_le
    {c x y : Real} (hc : 2 < c) :
    abs ((Real.sin x - Real.sin y) /
        sixVertexThetaDenominator c x y) <= 2 / (c ^ 2 - 4) := by
  have hbase : 0 < c ^ 2 - 4 := by nlinarith
  have hden : c ^ 2 - 4 <= sixVertexThetaDenominator c x y := by
    have hx := Real.neg_one_le_cos x
    have hy := Real.neg_one_le_cos y
    unfold sixVertexThetaDenominator sixVertexDelta
    nlinarith
  have hdenpos : 0 < sixVertexThetaDenominator c x y :=
    sixVertexThetaDenominator_pos hc x y
  have hnum : abs (Real.sin x - Real.sin y) <= 2 := by
    calc
      abs (Real.sin x - Real.sin y) <=
          abs (Real.sin x) + abs (Real.sin y) := abs_sub _ _
      _ <= 2 := by
        nlinarith [Real.abs_sin_le_one x, Real.abs_sin_le_one y]
  rw [abs_div, abs_of_pos hdenpos]
  exact (div_le_div_iff₀ hdenpos hbase).2 (by nlinarith)


theorem tendsto_sixVertexTheta_sub_linear_atTop (x y : Real -> Real) :
    Tendsto
      (fun c => sixVertexTheta c (x c) (y c) - (y c - x c))
      atTop (nhds 0) := by
  have hbound : Tendsto (fun c : Real => 2 / (c ^ 2 - 4))
      atTop (nhds 0) :=
    tendsto_sixVertexThetaQuadraticDenominator.const_div_atTop 2
  have hratio : Tendsto
      (fun c => (Real.sin (x c) - Real.sin (y c)) /
        sixVertexThetaDenominator c (x c) (y c)) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall (fun c => norm_nonneg _)
    · filter_upwards [eventually_gt_atTop (2 : Real)] with c hc
      change abs ((Real.sin (x c) - Real.sin (y c)) /
        sixVertexThetaDenominator c (x c) (y c)) <= 2 / (c ^ 2 - 4)
      exact sixVertexTheta_ratio_abs_le (x := x c) (y := y c) hc
    · exact hbound
  have harctan : Tendsto
      (fun c => Real.arctan
        ((Real.sin (x c) - Real.sin (y c)) /
          sixVertexThetaDenominator c (x c) (y c))) atTop (nhds 0) := by
    simpa using Real.continuousAt_arctan.tendsto.comp hratio
  have htwo := (tendsto_const_nhds.mul harctan :
    Tendsto (fun c => 2 * Real.arctan
      ((Real.sin (x c) - Real.sin (y c)) /
        sixVertexThetaDenominator c (x c) (y c))) atTop (nhds (2 * 0)))
  simpa [sixVertexTheta] using htwo


end
end StatMech.FrontierD
