/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeThermodynamicReduction
open Filter Set Topology


namespace StatMech.FrontierA

theorem cubicalSquareWilsonExpectation_pos
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    0 < cubicalSquareWilsonExpectation beta n := by
  let L := n + 1
  have hL : 0 < L := by omega
  dsimp [cubicalSquareWilsonExpectation, L]
  exact (gaugeWilsonExpectation_pos_iff_exists_boundary
    cubicalPlaquetteIncidence (fun _ : CubicalPlaquette L L L => beta)
      (fun _ => hbeta) (cubicalXYLoop (0 : Fin (L + 1)))).mpr
    ⟨cubicalXYSheet (0 : Fin (L + 1)),
      cubicalXYSheet_hasWilsonBoundary (0 : Fin (L + 1))⟩

@[simp] theorem cubicalSquareWilsonFreeEnergy_eq_neg_log
    (beta : Real) (n : Nat) :
    cubicalSquareWilsonFreeEnergy beta n =
      -Real.log (cubicalSquareWilsonExpectation beta n) := rfl


theorem cubicalSquareWilson_eventually_areaLaw
    {beta tau : Real} (hbeta : 0 < beta)
    (hlim : Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds tau))
    (htau : 0 < tau) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation beta n ≤
        Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
  apply eventual_areaLaw_of_logDensity_tendsto
    (cubicalSquareWilsonExpectation beta) tau
    (cubicalSquareWilsonExpectation_pos hbeta)
  · have heq : (fun n : Nat =>
        -Real.log (cubicalSquareWilsonExpectation beta n) /
          ((n + 1 : Nat) : Real) ^ 2) =
        cubicalSquareWilsonDensity beta := by
      funext n
      rfl
    rw [heq]
    exact hlim
  · exact htau


theorem cubicalSquareWilson_eventually_perimeterLaw
    {beta C : Real} (hbeta : 0 < beta)
    (hcost : ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonFreeEnergy beta n ≤
        C * ((n + 1 : Nat) : Real)) :
    ∀ᶠ n : Nat in atTop,
      Real.exp (-C * ((n + 1 : Nat) : Real)) ≤
        cubicalSquareWilsonExpectation beta n := by
  apply eventual_perimeterLaw_of_negLog_le
    (cubicalSquareWilsonExpectation beta) C
    (cubicalSquareWilsonExpectation_pos hbeta)
  filter_upwards [hcost] with n hn
  simpa only [cubicalSquareWilsonFreeEnergy_eq_neg_log] using hn


theorem cubicalSquareWilson_rate_pos_iff_below_critical
    {betaGauge betaIsingC tau : Real}
    (hGauge : 0 < betaGauge) (hIsingC : 0 < betaIsingC)
    (isingSurfaceTension : Real → Real)
    (hidentify : tau =
      isingSurfaceTension (gaugeDualCoupling betaGauge))
    (hphase : 0 < isingSurfaceTension (gaugeDualCoupling betaGauge) ↔
      betaIsingC < gaugeDualCoupling betaGauge) :
    0 < tau ↔ betaGauge < gaugeCriticalCoupling betaIsingC := by
  rw [hidentify, hphase]
  exact lt_gaugeDualCoupling_iff_lt_gaugeCriticalCoupling hGauge hIsingC


theorem cubicalSquareWilson_areaLaw_of_dual_surfaceTension
    {betaGauge betaIsingC tau : Real}
    (hGauge : 0 < betaGauge) (hIsingC : 0 < betaIsingC)
    (isingSurfaceTension : Real → Real)
    (hlim : Tendsto (cubicalSquareWilsonDensity betaGauge) atTop (nhds tau))
    (hidentify : tau =
      isingSurfaceTension (gaugeDualCoupling betaGauge))
    (hphase : 0 < isingSurfaceTension (gaugeDualCoupling betaGauge) ↔
      betaIsingC < gaugeDualCoupling betaGauge)
    (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
    ∀ᶠ n : Nat in atTop,
      cubicalSquareWilsonExpectation betaGauge n ≤
        Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
  apply cubicalSquareWilson_eventually_areaLaw hGauge hlim
  exact (cubicalSquareWilson_rate_pos_iff_below_critical
    hGauge hIsingC isingSurfaceTension hidentify hphase).2 hbelow

end StatMech.FrontierA
