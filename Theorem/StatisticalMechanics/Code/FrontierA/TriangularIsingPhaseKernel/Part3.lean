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
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingPhaseKernel.Part2
open Filter MeasureTheory Topology


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingCriticalInverseSymbolClamp_continuous
    {beta J c epsilon : Real} (hc : 0 < c) (hepsilon : 0 < epsilon) :
    Continuous (Function.uncurry
      (triangularIsingCriticalInverseSymbolClamp beta J c epsilon)) := by
  have hs := continuous_triangularIsingSymbol beta beta (beta * J)
  have hm : Continuous (fun z : Real × Real =>
      max (triangularIsingSymbol beta beta (beta * J) z.1 z.2)
        (c * epsilon ^ 2)) := hs.max continuous_const
  apply Continuous.div continuous_const hm
  intro z
  have hcut : 0 < c * epsilon ^ 2 := mul_pos hc (sq_pos_of_pos hepsilon)
  exact ne_of_gt (hcut.trans_le (le_max_right _ _))

theorem triangularIsingCriticalInverseSymbolClamp_eq
    {beta J c epsilon p q : Real} (hc : 0 < c)
    (hsize : epsilon ^ 2 <= p ^ 2 + q ^ 2)
    (hlower : c * (p ^ 2 + q ^ 2) <=
      triangularIsingSymbol beta beta (beta * J) p q) :
    triangularIsingCriticalInverseSymbolClamp beta J c epsilon p q =
      triangularIsingCriticalInverseSymbol beta J p q := by
  have hcut : c * epsilon ^ 2 <=
      triangularIsingSymbol beta beta (beta * J) p q :=
    (mul_le_mul_of_nonneg_left hsize hc.le).trans hlower
  rw [triangularIsingCriticalInverseSymbolClamp,
    triangularIsingCriticalInverseSymbol, max_eq_left hcut]


theorem triangularIsingCriticalInverseSymbol_inner_continuousOn
    {beta J epsilon : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hepsilon : 0 < epsilon) :
    ContinuousOn (fun x : Real =>
      ∫ y in x..(2 * x),
        triangularIsingCriticalInverseSymbol beta J x y)
      (Set.Icc epsilon 1) := by
  obtain ⟨c, hc, hlower⟩ :=
    exists_triangularIsingSymbol_quadratic_lower_at_root hbeta hroot
  let F : Real -> Real -> Real :=
    triangularIsingCriticalInverseSymbolClamp beta J c epsilon
  have hF : Continuous (Function.uncurry F) := by
    exact triangularIsingCriticalInverseSymbolClamp_continuous hc hepsilon
  have hmoving : Continuous (fun x : Real => ∫ y in x..(2 * x), F x y) :=
    StatMech.Onsager.ons_wedgeIntegral_continuous hF
  apply hmoving.continuousOn.congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le (by linarith [hepsilon.trans_le hx.1])] at hy
  have hx0 : 0 < x := hepsilon.trans_le hx.1
  have hy0 : 0 < y := hx0.trans_le hy.1
  have hxPi : |x| <= Real.pi := by
    rw [abs_of_pos hx0]
    exact hx.2.trans (by linarith [Real.pi_gt_three])
  have hyPi : |y| <= Real.pi := by
    rw [abs_of_pos hy0]
    have hyTwo : y <= 2 := hy.2.trans (by nlinarith [hx.2])
    exact hyTwo.trans (by linarith [Real.pi_gt_three])
  have hsize : epsilon ^ 2 <= x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg y, mul_self_le_mul_self hepsilon.le hx.1]
  exact (triangularIsingCriticalInverseSymbolClamp_eq hc
    hsize (hlower x y hxPi hyPi)).symm


theorem triangularIsingCriticalInverseSymbol_wedge_lower
    {beta J epsilon : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1)
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon <= 1) :
    (1 / (2 * (Real.sinh (2 * beta) / 2 +
        |Real.sinh (2 * (beta * J))|))) *
        ((2 / 5 : Real) * Real.log (1 / epsilon)) <=
      ∫ x in epsilon..1,
        ∫ y in x..(2 * x),
          triangularIsingCriticalInverseSymbol beta J x y := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hC : 0 < C := triangularIsingCriticalUpperCoefficient_pos hbeta
  have hcompCont : ContinuousOn (fun x : Real => 1 / (C * 5 * x))
      (Set.uIcc epsilon 1) := by
    rw [Set.uIcc_of_le hepsilonOne]
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact mul_ne_zero (mul_ne_zero hC.ne' (by norm_num))
      (ne_of_gt (hepsilon.trans_le hx.1))
  have hcomp : IntervalIntegrable (fun x : Real => 1 / (C * 5 * x))
      MeasureTheory.volume epsilon 1 := hcompCont.intervalIntegrable
  have hinnerCont :=
    triangularIsingCriticalInverseSymbol_inner_continuousOn
      hbeta hroot hepsilon
  have hinner : IntervalIntegrable (fun x : Real =>
      ∫ y in x..(2 * x),
        triangularIsingCriticalInverseSymbol beta J x y)
      MeasureTheory.volume epsilon 1 := by
    have hinnerCont' : ContinuousOn (fun x : Real =>
        ∫ y in x..(2 * x),
          triangularIsingCriticalInverseSymbol beta J x y)
        (Set.uIcc epsilon 1) := by
      simpa [Set.uIcc_of_le hepsilonOne] using hinnerCont
    exact hinnerCont'.intervalIntegrable
  have hmono := intervalIntegral.integral_mono_on hepsilonOne hcomp hinner
    (fun x hx => triangularIsingCriticalInverseSymbol_inner_lower
      hbeta hroot (hepsilon.trans_le hx.1)
        (by linarith [hx.2, Real.pi_gt_three]))
  have hcompEq :
      (∫ x in epsilon..1, 1 / (C * 5 * x)) =
        (1 / (2 * C)) * (2 / 5 : Real) * Real.log (1 / epsilon) := by
    calc
      (∫ x in epsilon..1, 1 / (C * 5 * x)) =
          (1 / (2 * C)) * ∫ x in epsilon..1, 2 / (5 * x) := by
            rw [← intervalIntegral.integral_const_mul]
            apply intervalIntegral.integral_congr
            intro x hx
            have hx0 : x ≠ 0 := by
              rw [Set.uIcc_of_le hepsilonOne] at hx
              exact (ne_of_gt (hepsilon.trans_le hx.1))
            field_simp
      _ = (1 / (2 * C)) * (2 / 5 : Real) * Real.log (1 / epsilon) := by
        rw [StatMech.Onsager.ons_logKernel_integral hepsilon hepsilonOne]
        ring
  rw [hcompEq] at hmono
  change (1 / (2 * C)) * ((2 / 5 : Real) * Real.log (1 / epsilon)) <= _
  calc
    (1 / (2 * C)) * ((2 / 5 : Real) * Real.log (1 / epsilon)) =
        (1 / (2 * C)) * (2 / 5 : Real) * Real.log (1 / epsilon) := by ring
    _ <= _ := hmono


theorem triangularIsingCriticalInverseSymbol_wedge_tendsto
    {beta J : Real} (hbeta : 0 < beta)
    (hroot : triangularIsingCriticalRate beta (beta * J) = 1) :
    Tendsto (fun n : Nat =>
      ∫ x in Real.exp (-(n : Real))..1,
        ∫ y in x..(2 * x),
          triangularIsingCriticalInverseSymbol beta J x y)
      atTop atTop := by
  let C := Real.sinh (2 * beta) / 2 +
    |Real.sinh (2 * (beta * J))|
  have hC : 0 < C := triangularIsingCriticalUpperCoefficient_pos hbeta
  apply Filter.tendsto_atTop_mono (fun n =>
    triangularIsingCriticalInverseSymbol_wedge_lower hbeta hroot
      (Real.exp_pos _) (by
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (Nat.cast_nonneg n)))
  have hlog := StatMech.Onsager.ons_logKernel_cutoff_tendsto 1 zero_lt_one
  have hscale := hlog.const_mul_atTop
    (show 0 < 1 / (2 * C) by positivity)
  simpa [C] using hscale

end
end StatMech.FrontierA
