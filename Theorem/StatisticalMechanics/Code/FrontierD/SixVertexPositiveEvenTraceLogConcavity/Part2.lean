/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveEvenTraceLogConcavity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoCycleCapacityHall.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part2
open Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorPerronLogConcave_of_positiveEvenTraceLogConcave
    (N : Nat) {c : Real} (hc : 0 < c)
    (htrace : SixVertexSectorPositiveEvenTraceLogConcave N c) :
    SixVertexSectorPerronLogConcave N c := by
  intro n hn0 hnN
  have hprev : n - 1 <= N := by omega
  have hmid : n <= N := hnN.le
  have hnext : n + 1 <= N := by omega
  let fprev : Nat -> Real := fun M =>
    Real.log (Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^
      sixVertexPositiveEvenHeight M)) / (sixVertexPositiveEvenHeight M : Real)
  let fmid : Nat -> Real := fun M =>
    Real.log (Matrix.trace (sixVertexSectorTransfer N n c ^
      sixVertexPositiveEvenHeight M)) / (sixVertexPositiveEvenHeight M : Real)
  let fnext : Nat -> Real := fun M =>
    Real.log (Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^
      sixVertexPositiveEvenHeight M)) / (sixVertexPositiveEvenHeight M : Real)
  have hprevLim : Tendsto fprev atTop
      (nhds (Real.log (sixVertexSectorPerronProfile N c (n - 1)))) := by
    simpa [fprev, sixVertexSectorPerronProfile_eq hprev] using
      (sixVertexSector_log_trace_div_height_tendsto_log_top hprev hc).comp
        tendsto_sixVertexPositiveEvenHeight
  have hmidLim : Tendsto fmid atTop
      (nhds (Real.log (sixVertexSectorPerronProfile N c n))) := by
    simpa [fmid, sixVertexSectorPerronProfile_eq hmid] using
      (sixVertexSector_log_trace_div_height_tendsto_log_top hmid hc).comp
        tendsto_sixVertexPositiveEvenHeight
  have hnextLim : Tendsto fnext atTop
      (nhds (Real.log (sixVertexSectorPerronProfile N c (n + 1)))) := by
    simpa [fnext, sixVertexSectorPerronProfile_eq hnext] using
      (sixVertexSector_log_trace_div_height_tendsto_log_top hnext hc).comp
        tendsto_sixVertexPositiveEvenHeight
  have hevent : ∀ᶠ M in atTop, fprev M + fnext M <= 2 * fmid M := by
    filter_upwards [] with M
    let H := sixVertexPositiveEvenHeight M
    have hH : 0 < H := sixVertexPositiveEvenHeight_pos M
    have hp : 0 < Matrix.trace
        (sixVertexSectorTransfer N (n - 1) c ^ H) :=
      sixVertexSector_trace_pow_pos hprev hc H
    have hm : 0 < Matrix.trace
        (sixVertexSectorTransfer N n c ^ H) :=
      sixVertexSector_trace_pow_pos hmid hc H
    have hn : 0 < Matrix.trace
        (sixVertexSectorTransfer N (n + 1) c ^ H) :=
      sixVertexSector_trace_pow_pos hnext hc H
    have hprod := htrace M n hn0 hnN
    have hlog :
        Real.log (Matrix.trace
            (sixVertexSectorTransfer N (n - 1) c ^ H)) +
          Real.log (Matrix.trace
            (sixVertexSectorTransfer N (n + 1) c ^ H)) <=
        2 * Real.log (Matrix.trace
          (sixVertexSectorTransfer N n c ^ H)) := by
      calc
        _ = Real.log
            (Matrix.trace (sixVertexSectorTransfer N (n - 1) c ^ H) *
              Matrix.trace (sixVertexSectorTransfer N (n + 1) c ^ H)) :=
          (Real.log_mul hp.ne' hn.ne').symm
        _ <= Real.log
            (Matrix.trace (sixVertexSectorTransfer N n c ^ H) ^ 2) :=
          Real.log_le_log (mul_pos hp hn) hprod
        _ = _ := by rw [Real.log_pow]; norm_num
    have hHreal : (0 : Real) < H := by exact_mod_cast hH
    have hdiv := (div_le_div_iff_of_pos_right hHreal).2 hlog
    calc
      fprev M + fnext M =
          (Real.log (Matrix.trace
              (sixVertexSectorTransfer N (n - 1) c ^ H)) +
            Real.log (Matrix.trace
              (sixVertexSectorTransfer N (n + 1) c ^ H))) / (H : Real) := by
        dsimp [fprev, fnext, H]
        ring
      _ <= 2 * Real.log
          (Matrix.trace (sixVertexSectorTransfer N n c ^ H)) / (H : Real) :=
        hdiv
      _ = 2 * fmid M := by
        dsimp [fmid, H]
        ring
  have hlogConcave :
      Real.log (sixVertexSectorPerronProfile N c (n - 1)) +
          Real.log (sixVertexSectorPerronProfile N c (n + 1)) <=
        2 * Real.log (sixVertexSectorPerronProfile N c n) :=
    le_of_tendsto_of_tendsto
      (hprevLim.add hnextLim) (tendsto_const_nhds.mul hmidLim) hevent
  have hp := sixVertexSectorPerronProfile_pos hprev hc
  have hm := sixVertexSectorPerronProfile_pos hmid hc
  have hn := sixVertexSectorPerronProfile_pos hnext hc
  have hlogProduct :
      Real.log (sixVertexSectorPerronProfile N c (n - 1) *
          sixVertexSectorPerronProfile N c (n + 1)) <=
        Real.log (sixVertexSectorPerronProfile N c n ^ 2) := by
    rw [Real.log_mul hp.ne' hn.ne', Real.log_pow]
    exact hlogConcave
  exact (Real.log_le_log_iff (mul_pos hp hn) (pow_pos hm 2)).1 hlogProduct


end
end StatMech.FrontierD
