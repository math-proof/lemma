/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity
open Filter MeasureTheory Topology


namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_logConcave
    {q : Real} (hq : 4 < q) (r : Nat)
    (hlc : ∀ᶠ k in atTop, SixVertexSectorPerronLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [hlc] with k hk
  exact fkRectBalancedShareSpectralGap_eq_zero_of_logConcave hq r k hk


theorem
    tendsto_fkRectBalancedShareSpectralGap_zero_of_eventually_traceLogConcave
    {q : Real} (hq : 4 < q) (r : Nat)
    (hlc : ∀ᶠ k in atTop, SixVertexSectorTraceLogConcave
      (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [hlc] with k hk
  exact fkRectBalancedShareSpectralGap_eq_zero_of_traceLogConcave hq r k hk


theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_keyCapacityHall
    {q : Real} (hq : 4 < q) (r : Nat)
    (hHall : SixVertexCanonicalPositiveEvenTraceKeyCapacityHall) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (tendsto_congr' ?_).2 tendsto_const_nhds
  filter_upwards [] with k
  exact
    fkRectBalancedShareSpectralGap_eq_zero_of_positiveEvenTraceKeyCapacityHall
      hq r k (hHall r k)


theorem fkRectBalancedShareSpectralGap_eq_base_shift
    (q : Real) (r k : Nat) :
    fkRectBalancedShareSpectralGap q r k =
      fkRectBalancedShareSpectralGap q 0 (k + r) := by
  simp [fkRectBalancedShareSpectralGap, sixVertexFourWidth,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


theorem tendsto_fkRectBalancedShareSpectralGap_zero_of_base
    {q : Real}
    (hgap : Tendsto (fkRectBalancedShareSpectralGap q 0)
      atTop (nhds 0)) (r : Nat) :
    Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
  apply (hgap.comp (tendsto_add_atTop_nat r)).congr'
  filter_upwards [] with k
  exact (fkRectBalancedShareSpectralGap_eq_base_shift q r k).symm


end
end StatMech.FrontierD
