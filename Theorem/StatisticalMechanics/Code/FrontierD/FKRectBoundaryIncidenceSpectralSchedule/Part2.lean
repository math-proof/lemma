/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceSpectralSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareVerticalRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAllSectorWidthRate
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceRateCapstone
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule
open Filter Topology MeasureTheory


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

theorem fkRectBalancedSectorShare_fixedCharge_vertical_negLog_tendsto
    {q : Real} (hq : 4 < q) (r k : Nat) :
    Tendsto (fun m =>
      -Real.log (fkRectBalancedSectorShare
          (fkRectFixedChargeVerticalFamily r k m) q) /
        (fkRectFixedChargeVerticalFamily r k m).height)
      atTop (nhds (fkRectBalancedShareSpectralGap q r k)) := by
  have hindex : Tendsto (fun m : Nat => 2 * (m + 2)) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 <| ⟨N, fun m hm => by omega⟩
  have h := (sixVertexBalancedTraceShare_negLog_div_height_tendsto
    (sixVertexFourWidth r (k + 1))
    (sixVertexFourWidth_even r (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq] :
      0 < fkQgt4SixVertexWeight q)).comp hindex
  apply h.congr'
  filter_upwards [] with m
  rw [fkRectFixedChargeVerticalFamily_balancedShare_eq_traceShare r k m hq]
  simp only [fkRectFixedChargeVerticalFamily_medialWidth,
    fkRectFixedChargeVerticalFamily_medialHeight,
    fkRectFixedChargeVerticalFamily_height, Function.comp_apply]


end
end StatMech.FrontierD
