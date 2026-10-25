/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAlmostAdditive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingAlmostAdditive.Part2
open Filter Set


namespace StatMech.FrontierA

namespace QuantumIsingAlmostAdditive

variable {u : Nat -> Real} {c : Real}

theorem tendsto_limit (h : QuantumIsingAlmostAdditive u c) :
    Tendsto (fun n => u n / n) atTop (nhds h.limit) := by
  have hshift := h.shift_subadditive.tendsto_lim h.shift_bddBelow
  have hc : Tendsto (fun n : Nat => c / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hsub := hshift.sub hc
  convert hsub using 1
  · funext n
    ring
  · simp [limit]


theorem abs_limit_sub_div_le (h : QuantumIsingAlmostAdditive u c)
    {L : Nat} (hL : L ≠ 0) :
    |h.limit - u L / L| ≤ c / L := by
  let hplus := h.shift_subadditive
  have hbplus := h.shift_bddBelow
  have hupp : h.limit ≤ (u L + c) / L := by
    exact hplus.lim_le_div hbplus hL
  let hneg := h.neg
  have hnegLim : hneg.limit = -h.limit := by
    have hconv : Tendsto (fun n : Nat => (-u n) / n)
        atTop (nhds (-h.limit)) := by
      convert h.tendsto_limit.neg using 1
      funext n
      ring
    exact tendsto_nhds_unique hneg.tendsto_limit hconv
  have hlowRaw : hneg.limit ≤ ((-u L) + c) / L := by
    exact hneg.shift_subadditive.lim_le_div hneg.shift_bddBelow hL
  rw [hnegLim] at hlowRaw
  rw [abs_le]
  constructor
  · rw [add_div] at hlowRaw
    have hnegdiv : (-u L) / (L : Real) = -(u L / L) := by ring
    rw [hnegdiv] at hlowRaw
    linarith
  · rw [add_div] at hupp
    linarith

end QuantumIsingAlmostAdditive
end StatMech.FrontierA
