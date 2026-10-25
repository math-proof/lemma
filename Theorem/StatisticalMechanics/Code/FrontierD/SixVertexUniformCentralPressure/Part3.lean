/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceParticleHole
import Def.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem
    sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorPositiveEvenTraceLogConcave N c) :
    SixVertexPositiveEvenHeightCentralTraceMaximal N c := by
  intro M n hn
  let a : Nat -> Real := fun sector => Matrix.trace
    (sixVertexSectorTransfer N sector c ^ sixVertexPositiveEvenHeight M)
  have hpos : forall sector, sector <= N -> 0 < a sector := by
    intro sector hsector
    exact sixVertexSector_trace_pow_pos hsector hc _
  have hsym : forall sector, sector <= N ->
      a (N - sector) = a sector := by
    intro sector hsector
    exact sixVertexSectorTrace_particleHole_uniformPressure hsector _ c
  have hlocal : forall sector, 0 < sector -> sector < N ->
      a (sector - 1) * a (sector + 1) <= a sector ^ 2 := by
    intro sector hsector0 hsectorN
    exact hlc M sector hsector0 hsectorN
  change a n <= a (N / 2)
  by_cases hnHalf : n <= N / 2
  · exact lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal hnHalf
  · rw [← hsym n hn]
    apply lowerHalf_le_middle_of_pos_logConcave_symmetric
      a N hN hpos hsym hlocal
    obtain ⟨half, rfl⟩ := hN
    omega


theorem
    sixVertexPositiveEvenHeight_full_le_card_mul_central_of_traceLogConcave
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hlc : SixVertexSectorPositiveEvenTraceLogConcave N c)
    (M : Nat) :
    sixVertexFixedWidthPartitionSum N (sixVertexPositiveEvenHeight M) c <=
      (N + 1 : Nat) * Matrix.trace
        (sixVertexSectorTransfer N (N / 2) c ^
          sixVertexPositiveEvenHeight M) := by
  have hmax :=
    sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave
      N hN hc hlc
  rw [sixVertexFixedWidthPartitionSum_eq_sum_sector_traces N
    (sixVertexPositiveEvenHeight M) (sixVertexPositiveEvenHeight_pos M)]
  calc
    _ <= ∑ _sector : Fin (N + 1), Matrix.trace
        (sixVertexSectorTransfer N (N / 2) c ^
          sixVertexPositiveEvenHeight M) := by
      apply Finset.sum_le_sum
      intro sector _
      exact hmax M sector.val (by omega)
    _ = _ := by simp

theorem sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c)
    (hbound : SixVertexUniformHeightCentralTraceBound N c) :
    sixVertexWidthTopEigenvalue N c =
      sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c := by
  obtain ⟨C, hC, hbound⟩ := hbound
  let gap : Nat -> Real := fun M =>
    -Real.log (sixVertexBalancedTraceShare N M c) / (M : Real)
  have hgapLimit : Tendsto gap atTop
      (nhds (Real.log (sixVertexWidthTopEigenvalue N c) -
        Real.log (sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c))) := by
    simpa [gap, sixVertexLambda] using
      sixVertexBalancedTraceShare_negLog_div_height_tendsto N hN hc
  have hgapZero : Tendsto gap atTop (nhds 0) := by
    apply squeeze_zero
    · intro M
      by_cases hM : 0 < M
      · have hshare := sixVertexBalancedTraceShare_mem_Ioc N M hM hc
        exact div_nonneg (neg_nonneg.mpr
          (Real.log_nonpos hshare.1.le hshare.2)) (by positivity)
      · simp [gap, Nat.eq_zero_of_not_pos hM]
    · intro M
      by_cases hM : 0 < M
      · have hcentral : 0 < Matrix.trace
          (sixVertexSectorTransfer N (N / 2) c ^ M) :=
          sixVertexSector_trace_pow_pos (Nat.div_le_self N 2) hc M
        have hfull : 0 < sixVertexFixedWidthPartitionSum N M c :=
          sixVertexFixedWidthPartitionSum_pos N M hM hc
        have hratio : (1 : Real) / C <=
            sixVertexBalancedTraceShare N M c := by
          rw [sixVertexBalancedTraceShare, le_div_iff₀ hfull]
          have h := hbound M hM
          rw [div_mul_eq_mul_div, div_le_iff₀ hC]
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have hlog : -Real.log (sixVertexBalancedTraceShare N M c) <=
            Real.log C := by
          have hratioPos : 0 < (1 : Real) / C := by positivity
          have hmono := Real.log_le_log hratioPos hratio
          rw [Real.log_div (by norm_num : (1 : Real) ≠ 0) hC.ne',
            Real.log_one] at hmono
          linarith
        exact div_le_div_of_nonneg_right hlog (by positivity)
      · simp [gap, Nat.eq_zero_of_not_pos hM]
    · simpa using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun M : Nat => Real.log C / (M : Real)) atTop (nhds 0))
  have hgapEq :
      Real.log (sixVertexWidthTopEigenvalue N c) -
          Real.log (sixVertexSectorTopEigenvalue N (N / 2)
            (Nat.div_le_self N 2) c) = 0 :=
    tendsto_nhds_unique hgapLimit hgapZero
  have htop : 0 < sixVertexWidthTopEigenvalue N c :=
    sixVertexWidthTopEigenvalue_pos N hc
  have hcentral : 0 < sixVertexSectorTopEigenvalue N (N / 2)
      (Nat.div_le_self N 2) c :=
    sixVertexSectorTopEigenvalue_pos (Nat.div_le_self N 2) hc
  have hlog : Real.log (sixVertexWidthTopEigenvalue N c) =
      Real.log (sixVertexSectorTopEigenvalue N (N / 2)
        (Nat.div_le_self N 2) c) := by
    linarith
  calc
    sixVertexWidthTopEigenvalue N c =
        Real.exp (Real.log (sixVertexWidthTopEigenvalue N c)) :=
      (Real.exp_log htop).symm
    _ = Real.exp (Real.log (sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c)) := congrArg Real.exp hlog
    _ = sixVertexSectorTopEigenvalue N (N / 2)
          (Nat.div_le_self N 2) c := Real.exp_log hcentral


end
end StatMech.FrontierD
