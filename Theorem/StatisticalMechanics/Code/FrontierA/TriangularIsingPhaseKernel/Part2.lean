/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbolBounds
import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part12
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingPhaseKernel
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingCriticalInverseSymbol_lower_on_wedge
    {beta J x y : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hx : 0 < x) (h2xPi : 2 * x <= Real.pi)
    (hxy : x <= y) (hy2x : y <= 2 * x) :
    1 / ((Real.sinh (2 * beta) / 2 +
          |Real.sinh (2 * (beta * J))|) * 5 * x ^ 2) <=
      triangularIsingCriticalInverseSymbol beta J x y := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hC : 0 < C := triangularIsingCriticalUpperCoefficient_pos hbeta
  have hxPi : |x| <= Real.pi := by rw [abs_of_pos hx]; linarith
  have hy0 : 0 < y := hx.trans_le hxy
  have hyPi : |y| <= Real.pi := by rw [abs_of_pos hy0]; linarith
  have hs : 0 < triangularIsingSymbol beta beta (beta * J) x y :=
    triangularIsingSymbol_pos_at_root_of_ne_zero
      hbeta hroot hxPi hyPi (Or.inl hx.ne')
  have hu := triangularIsingSymbol_quadratic_upper_at_root
    (p := x) (q := y) hbeta hroot
  change triangularIsingSymbol beta beta (beta * J) x y <=
    C * (x ^ 2 + y ^ 2) at hu
  have hySq : y ^ 2 <= 4 * x ^ 2 := by nlinarith
  have hupper : triangularIsingSymbol beta beta (beta * J) x y <=
      C * 5 * x ^ 2 := by
    calc
      triangularIsingSymbol beta beta (beta * J) x y <=
          C * (x ^ 2 + y ^ 2) := hu
      _ <= C * 5 * x ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left hySq hC.le]
  unfold triangularIsingCriticalInverseSymbol
  exact one_div_le_one_div_of_le hs hupper


theorem triangularIsingCriticalInverseSymbol_inner_lower
    {beta J x : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hx : 0 < x) (h2xPi : 2 * x <= Real.pi) :
    1 / ((Real.sinh (2 * beta) / 2 +
          |Real.sinh (2 * (beta * J))|) * 5 * x) <=
      ∫ y in x..(2 * x),
        triangularIsingCriticalInverseSymbol beta J x y := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hx2x : x <= 2 * x := by linarith
  have hconst : IntervalIntegrable (fun _y : Real => 1 / (C * 5 * x ^ 2))
      MeasureTheory.volume x (2 * x) := continuousOn_const.intervalIntegrable
  have hkernelCont : ContinuousOn
      (fun y : Real => triangularIsingCriticalInverseSymbol beta J x y)
      (Set.uIcc x (2 * x)) := by
    unfold triangularIsingCriticalInverseSymbol
    apply ContinuousOn.div continuousOn_const
        (by unfold triangularIsingSymbol; fun_prop)
    · intro y hy
      rw [Set.uIcc_of_le hx2x] at hy
      have hxPi : |x| <= Real.pi := by rw [abs_of_pos hx]; linarith
      have hy0 : 0 < y := hx.trans_le hy.1
      have hyPi : |y| <= Real.pi := by
        rw [abs_of_pos hy0]
        exact hy.2.trans h2xPi
      exact (triangularIsingSymbol_pos_at_root_of_ne_zero
        hbeta hroot hxPi hyPi (Or.inl hx.ne')).ne'
  have hkernel : IntervalIntegrable
      (fun y : Real => triangularIsingCriticalInverseSymbol beta J x y)
      MeasureTheory.volume x (2 * x) :=
    hkernelCont.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hx2x hconst hkernel
    (fun y hy => triangularIsingCriticalInverseSymbol_lower_on_wedge
      hbeta hroot hx h2xPi hy.1 hy.2)
  rw [intervalIntegral.integral_const] at hmono
  norm_num only [smul_eq_mul] at hmono
  change 1 / (C * 5 * x) <= _
  convert hmono using 1
  field_simp
  ring


end
end StatMech.FrontierA
