/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing.Part4
open Filter Set Topology


namespace StatMech.FrontierA

theorem eventual_areaLaw_of_logDensity_tendsto
    (w : Nat → Real) (tau : Real)
    (hw : ∀ n, 0 < w n)
    (hlim : Tendsto (fun n : Nat =>
      -Real.log (w n) / ((n + 1 : Nat) : Real) ^ 2)
      atTop (nhds tau))
    (htau : 0 < tau) :
    ∀ᶠ n : Nat in atTop,
      w n ≤ Real.exp (-(tau / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
  have hhalf : tau / 2 < tau := by linarith
  have hevent := hlim.eventually (Ioi_mem_nhds hhalf)
  filter_upwards [hevent] with n hn
  have harea : (0 : Real) < ((n + 1 : Nat) : Real) ^ 2 := by positivity
  have hscaled : (tau / 2) * ((n + 1 : Nat) : Real) ^ 2 <
      -Real.log (w n) := (lt_div_iff₀ harea).mp hn
  have hlog : Real.log (w n) <
      -(tau / 2) * ((n + 1 : Nat) : Real) ^ 2 := by linarith
  have hexp := (Real.exp_lt_exp.mpr hlog).le
  rw [Real.exp_log (hw n)] at hexp
  exact hexp


theorem eventual_perimeterLaw_of_negLog_le
    (w : Nat → Real) (C : Real)
    (hw : ∀ n, 0 < w n)
    (hcost : ∀ᶠ n : Nat in atTop,
      -Real.log (w n) ≤ C * ((n + 1 : Nat) : Real)) :
    ∀ᶠ n : Nat in atTop,
      Real.exp (-C * ((n + 1 : Nat) : Real)) ≤ w n := by
  filter_upwards [hcost] with n hn
  have hlog : -C * ((n + 1 : Nat) : Real) ≤ Real.log (w n) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (hw n)] at hexp
  exact hexp


end StatMech.FrontierA
