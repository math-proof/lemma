/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingIntegralAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingWeakAntiferromagnetic
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
open Filter MeasureTheory Topology Complex


namespace StatMech.FrontierA

noncomputable section

theorem differentiableOn_triangularIsingFreeEnergyRayComplex
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    DifferentiableOn Complex (triangularIsingFreeEnergyRayComplex J)
      (triangularIsingComplexNeighborhood beta J) := by
  intro z hz
  unfold triangularIsingFreeEnergyRayComplex
  exact ((hasDerivAt_const z (-(Real.log 2 : Complex))).sub
    ((hasDerivAt_triangularIsingComplexDoubleIntegral
      hbeta hcrit hz).const_mul
        (1 / (8 * Real.pi ^ 2) : Complex))).differentiableAt.differentiableWithinAt

theorem analyticAt_triangularIsingFreeEnergyRayComplex
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Complex (triangularIsingFreeEnergyRayComplex J) beta := by
  exact (differentiableOn_triangularIsingFreeEnergyRayComplex
    hbeta hcrit).analyticAt
      (triangularIsingComplexNeighborhood_mem_nhds hbeta hcrit)

theorem triangularIsingComplexLog_ofReal
    {beta J b : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J)
    (p q : Real) :
    Complex.log (triangularIsingRaySymbolComplex J b p q) =
      (Real.log (triangularIsingSymbol b b (b * J) p q) : Complex) := by
  rw [triangularIsingRaySymbolComplex_ofReal]
  have hpos : 0 < triangularIsingSymbol b b (b * J) p q := by
    have := triangularIsingRaySymbolComplex_re_pos
      hbeta hcrit hb p q
    simpa [triangularIsingRaySymbolComplex_ofReal] using this
  exact (Complex.ofReal_log hpos.le).symm

theorem triangularIsingComplexDoubleIntegral_ofReal
    {beta J b : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
    (∫ p in (-Real.pi)..Real.pi,
      ∫ q in (-Real.pi)..Real.pi,
        Complex.log (triangularIsingRaySymbolComplex J b p q)) =
      Complex.ofReal (∫ p in (-Real.pi)..Real.pi,
        ∫ q in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol b b (b * J) p q)) := by
  calc
    _ = ∫ p in (-Real.pi)..Real.pi,
        Complex.ofReal (∫ q in (-Real.pi)..Real.pi,
          Real.log (triangularIsingSymbol b b (b * J) p q)) := by
      apply intervalIntegral.integral_congr
      intro p _hp
      calc
        _ = ∫ q in (-Real.pi)..Real.pi,
            (Real.log (triangularIsingSymbol b b (b * J) p q) : Complex) := by
          apply intervalIntegral.integral_congr
          intro q _hq
          exact triangularIsingComplexLog_ofReal hbeta hcrit hb p q
        _ = _ := intervalIntegral.integral_ofReal
    _ = _ := intervalIntegral.integral_ofReal

theorem triangularIsingFreeEnergyRayComplex_ofReal
    {beta J b : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1)
    (hb : (b : Complex) ∈ triangularIsingComplexNeighborhood beta J) :
    triangularIsingFreeEnergyRayComplex J b =
      (triangularIsingFreeEnergyValue b b (b * J) : Complex) := by
  unfold triangularIsingFreeEnergyRayComplex triangularIsingFreeEnergyValue
  rw [triangularIsingComplexDoubleIntegral_ofReal hbeta hcrit hb]
  push_cast
  ring


theorem triangularIsingFreeEnergyValue_analyticAt_of_noncritical
    {beta J : Real} (hbeta : 0 < beta)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta := by
  have hc := (analyticAt_triangularIsingFreeEnergyRayComplex
    hbeta hcrit).re_ofReal
  apply hc.congr
  have hev : ∀ᶠ b : Real in nhds beta,
      (b : Complex) ∈ triangularIsingComplexNeighborhood beta J :=
    (Complex.continuous_ofReal.tendsto beta)
      (triangularIsingComplexNeighborhood_mem_nhds hbeta hcrit)
  filter_upwards [hev] with b hb
  rw [triangularIsingFreeEnergyRayComplex_ofReal hbeta hcrit hb]
  simp


theorem triangularIsingFreeEnergyValue_analyticAt_of_gt_neg_one_noncritical
    {beta J : Real} (hbeta : 0 < beta) (_hJ : -1 < J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta hcrit


theorem triangularIsingCriticalRate_ne_one_of_le_neg_one
    {beta J : Real} (hbeta : 0 < beta) (hJ : J <= -1) :
    triangularIsingCriticalRate beta (beta * J) ≠ 1 := by
  intro hcrit
  have hzero : triangularIsingSymbol beta beta (beta * J) 0 0 = 0 :=
    (triangularIsingSymbol_zero_iff_criticalRate_eq_one hbeta).2 hcrit
  have hthird : beta * J <= -beta := by
    nlinarith
  exact (triangularIsingSymbol_pos_of_third_le_neg hbeta hthird 0 0).ne' hzero


theorem triangularIsingFreeEnergyValue_analyticAt_of_le_neg_one
    {beta J : Real} (hbeta : 0 < beta) (hJ : J <= -1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta
    (triangularIsingCriticalRate_ne_one_of_le_neg_one hbeta hJ)

theorem triangularIsingFreeEnergyValue_analyticAt_of_nonnegative_noncritical
    {beta J : Real} (hbeta : 0 < beta) (_hJ : 0 <= J)
    (hcrit : triangularIsingCriticalRate beta (beta * J) ≠ 1) :
    AnalyticAt Real
      (fun b => triangularIsingFreeEnergyValue b b (b * J)) beta :=
  triangularIsingFreeEnergyValue_analyticAt_of_noncritical hbeta hcrit

end
end StatMech.FrontierA
