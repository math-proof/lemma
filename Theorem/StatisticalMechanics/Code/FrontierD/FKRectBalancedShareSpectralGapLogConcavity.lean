/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part3
open Filter MeasureTheory Topology


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

theorem fkRectBalancedShareSpectralGap_eq_zero_of_logConcave
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hlc : SixVertexSectorPerronLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  let N := sixVertexFourWidth r (k + 1)
  let c := fkQgt4SixVertexWeight q
  have hc : 0 < c := by
    dsimp [c]
    linarith [two_lt_fkQgt4SixVertexWeight hq]
  have htop := sixVertexWidthTopEigenvalue_eq_halfFilled_of_logConcave
    N (sixVertexFourWidth_even r (k + 1)) hc hlc
  have hlambda :
      sixVertexLambda N 0 (sixVertexFourWidth_even r (k + 1))
          (Nat.zero_le _) c =
        sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c := by
    simp [sixVertexLambda]
  unfold fkRectBalancedShareSpectralGap
  change Real.log (sixVertexWidthTopEigenvalue N c) -
      Real.log (sixVertexLambda N 0 (sixVertexFourWidth_even r (k + 1))
        (Nat.zero_le _) c) = 0
  rw [htop, hlambda]
  ring


theorem fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hlc : SixVertexSectorTraceLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  apply fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k
  exact sixVertexSectorPerronLogConcave_of_traceLogConcave
    (sixVertexFourWidth r (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq]) hlc


theorem
    fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall
    {q : Real} (hq : 4 < q) (r k : Nat)
    (hHall : SixVertexPositiveEvenTraceKeyCapacityHall
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))) :
    fkRectBalancedShareSpectralGap q r k = 0 := by
  apply fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k
  exact sixVertexSectorPerronLogConcave_of_positiveEvenTraceKeyCapacityHall
    (sixVertexFourWidth r (k + 1))
    (sixVertexFourWidth_pos r (k + 1))
    (sixVertexFourWidth_even r (k + 1))
    (by linarith [two_lt_fkQgt4SixVertexWeight hq]) hHall


end
end StatMech.FrontierD
