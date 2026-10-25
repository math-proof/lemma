/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxSharpness
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePercolationFull
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCritical

open Filter

open WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


theorem wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
    (d n : Nat) (hn : 1 <= n) (q beta : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) :
    wiredOuterInnerTheta d q beta n =
      (FK.wiredFiniteMeasure d (2 * n)
          (by
            have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
            linarith : 0 < 1 - Real.exp (-beta))
          (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
          (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (FK.boxBdryConnEvent d n) := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hevent : boxRestrict d (2 * n) ⁻¹' centeredShellEvent d n =
      FK.boxBdryConnEvent d n := by
    rw [centeredShellEvent_eq_connToBdryEventLE d n hn,
      ← FK.boxBdryConnEvent_eq_boxRestrict_preimage d (n_le_two_mul n)]
  have hmeas : MeasurableSet
      (boxRestrict d (2 * n) ⁻¹' centeredShellEvent d n) := by
    rw [hevent]
    exact FK.measurableSet_boxBdryConnEvent d n
  have hmass := FK.fkgq_wiredFiniteMeasure_real_boxRestrictEvent
    (d := d) (2 * n) hp hp1 (zero_lt_one.trans_le hq)
    (centeredShellEvent d n) hmeas
  have htheta := wiredOuterInnerTheta_eq_centeredShellMass
    d n hn q beta hq hbeta
  rw [hevent] at hmass
  change wiredOuterInnerTheta d q beta n =
    (FK.wiredFiniteMeasure d (2 * n) hp hp1
      (zero_lt_one.trans_le hq) : Measure _).real
        (FK.boxBdryConnEvent d n)
  rw [htheta]
  exact hmass.symm


theorem wiredOuterInnerTheta_tendsto_fkTheta
    (d : Nat) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredOuterInnerTheta d q beta n) atTop
      (nhds (FK.fkTheta d
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) (q := q))) := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
    linarith
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  let a : Nat → Real := fun n =>
    (FK.wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq) :
      Measure (ConfigSpace (Sym2 (Site d)))).real (FK.boxBdryConnEvent d n)
  let b : Nat → Real := fun n => wiredOuterInnerTheta d q beta n
  let thetaInf := FK.fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q)
  have ha : Tendsto a atTop (nhds thetaInf) := by
    simpa [a, thetaInf] using
      FK.fkgq_boxBdryConnEvent_diag_tendsto (d := d) hp hp1 hq
  have htwo : Tendsto (fun n : Nat => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 (fun N => ?_)
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have ha2 : Tendsto (fun n => a (2 * n)) atTop (nhds thetaInf) := ha.comp htwo
  have hlower : ∀ᶠ n in atTop, a (2 * n) <= b n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [show b n =
        (FK.wiredFiniteMeasure d (2 * n) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxBdryConnEvent d n) by
      simpa [b, p] using
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
          d n hn q beta hq hbeta]
    exact measureReal_mono
      (FK.boxBdryConnEvent_subset_le n (2 * n) hn (n_le_two_mul n))
      (measure_ne_top _ _)
  have hupper : ∀ᶠ n in atTop, b n <= a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [show b n =
        (FK.wiredFiniteMeasure d (n + n) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxBdryConnEvent d n) by
      simpa [b, p, two_mul] using
        wiredOuterInnerTheta_eq_wiredFiniteMeasure_double
          d n hn q beta hq hbeta]
    let A : Set (ConfigSpace (Sym2 (boxVerts d n))) :=
      {omega | IsingFK.ConnToBdry (boxGraph d n) (boxBoundary d n) omega
        (IsingFK.boxOrigin d n)}
    have hanti : Antitone (fun k =>
        (FK.wiredFiniteMeasure d (n + k) hp hp1
          (zero_lt_one.trans_le hq) : Measure _).real
            (FK.boxBdryConnEvent d n)) := by
      apply antitone_nat_of_succ_le
      intro k
      simpa [A, Nat.add_assoc] using
        (FK.fkgq_wired_succ (d := d) n (n + k) (Nat.le_add_right n k)
          hp hp1 hq (S := A) (isIncreasing_connToBdryEvent n))
    have h := hanti (Nat.zero_le n)
    simpa [a, Nat.add_zero, two_mul] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ha2 ha hlower hupper


theorem wiredThresholdTheta_tendsto_fkTheta_div
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredThresholdTheta d q beta0 n beta) atTop
      (nhds (FK.fkTheta d
        (by
          have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
          linarith : 0 < 1 - Real.exp (-beta))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) (q := q) / wiredSharpConstant d beta0)) := by
  have hraw := wiredOuterInnerTheta_tendsto_fkTheta d q beta hq hbeta
  have hdiv := hraw.div_const (wiredSharpConstant d beta0)
  simpa [wiredThresholdTheta, not_le.mpr hbeta, wiredNormalizedTheta] using hdiv


theorem wiredThresholdSet_mem_of_fkTheta_pos
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hTheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q)) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n b) := by
  let L := FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q) / wiredSharpConstant d beta0
  have hL : 0 < L := div_pos hTheta (wiredSharpConstant_pos d beta0)
  have hconv : Tendsto (fun n => wiredThresholdTheta d q beta0 n beta)
      atTop (nhds L) := by
    simpa [L] using
      wiredThresholdTheta_tendsto_fkTheta_div d q beta0 beta hq hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 <= limsup (BetaThresholdBound.logRatio (fun n =>
    IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta)) atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]


theorem wiredThresholdSet_nonempty (d : Nat) (q beta0 : Real)
    (hd : 2 <= d) (hq : 1 <= q) :
    (BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n b)).Nonempty := by
  let pc := FK.fkPc d q
  let p := (pc + 1) / 2
  let beta := -Real.log (1 - p)
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd hq
  have hpc1 : pc < 1 := FK.fkPc_lt_one_of_two_le hd hq
  have hp : 0 < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hpcp : pc < p := by dsimp [p]; linarith
  have hremain : 0 < 1 - p := by linarith
  have hremain1 : 1 - p < 1 := by linarith
  have hbeta : 0 < beta := by
    dsimp [beta]
    exact neg_pos.mpr (Real.log_neg hremain hremain1)
  have hparam : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    rw [neg_neg, Real.exp_log hremain]
    ring
  have hthetaP : 0 < FK.fkTheta d hp hp1
      (zero_lt_one.trans_le hq) (q := q) :=
    FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1
      (zero_lt_one.trans_le hq) hpcp
  have hthetaBeta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q) := by
    simpa only [hparam] using hthetaP
  exact ⟨beta, wiredThresholdSet_mem_of_fkTheta_pos
    d q beta0 beta hq hbeta hthetaBeta⟩


end WiredBoxCritical
end OSSS
end StatMech
