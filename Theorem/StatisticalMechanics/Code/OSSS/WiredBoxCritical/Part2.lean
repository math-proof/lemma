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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxCritical
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCritical

open Filter

open WiredBoxSharpness

open Lattice FK

open WiredBoxLocalized WiredBoxOffCentre

open MeasureTheory


theorem betaFKTheta_eq (d : Nat) (beta : Real) (hbeta : 0 < beta) :
    betaFKTheta d beta = FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) := by
  simp only [betaFKTheta, dif_pos hbeta]

theorem betaFKTheta_nonneg (d : Nat) (beta : Real) :
    0 <= betaFKTheta d beta := by
  by_cases hbeta : 0 < beta
  · rw [betaFKTheta_eq d beta hbeta]
    exact FK.fkTheta_nonneg d _ _ (by norm_num) (q := 2)
  · simp [betaFKTheta, hbeta]


theorem betaFKTheta_mono (d : Nat) : Monotone (betaFKTheta d) := by
  intro a b hab
  by_cases hb : 0 < b
  · by_cases ha : 0 < a
    · rw [betaFKTheta_eq d a ha, betaFKTheta_eq d b hb]
      have hpa0 : 0 < 1 - Real.exp (-a) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -a < 0)
        linarith
      have hpa1 : 1 - Real.exp (-a) < 1 := by
        linarith [Real.exp_pos (-a)]
      have hpb0 : 0 < 1 - Real.exp (-b) := by
        have := Real.exp_lt_one_iff.mpr (by linarith : -b < 0)
        linarith
      have hpb1 : 1 - Real.exp (-b) < 1 := by
        linarith [Real.exp_pos (-b)]
      have hexp : Real.exp (-b) <= Real.exp (-a) :=
        Real.exp_le_exp.mpr (by linarith)
      have hpab : 1 - Real.exp (-a) <= 1 - Real.exp (-b) := by
        simpa only [sub_eq_add_neg, add_comm] using
          add_le_add_left (neg_le_neg hexp) 1
      exact FK.fkgq_fkTheta_monotone_in_p hpa0 hpa1 hpb0 hpb1 hpab
        (by norm_num)
    · rw [show betaFKTheta d a = 0 by simp [betaFKTheta, ha]]
      exact betaFKTheta_nonneg d b
  · have ha : ¬ 0 < a := fun h => hb (h.trans_le hab)
    simp [betaFKTheta, ha, hb]


theorem wiredThresholdSet_nonempty_q2 (d : Nat) (beta0 : Real) (hd : 2 <= d) :
    (BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n b)).Nonempty := by
  let pc := FK.fkPc d 2
  let p := (pc + 1) / 2
  let beta := -Real.log (1 - p)
  have hpc0 : 0 < pc := FK.fkPc_pos_of_two_le hd (by norm_num)
  have hpc1 : pc < 1 := FK.fkPc_two_lt_one_of_two_le hd
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
  have hthetaP : 0 < FK.fkTheta d hp hp1 (by norm_num : (0 : Real) < 2)
      (q := 2) :=
    FK.frp_fkTheta_pos_of_gt_fkPc d hp hp1 (by norm_num) hpcp
  have hthetaBeta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) := by
    simpa only [hparam] using hthetaP
  exact wiredThresholdSet_nonempty_of_fkTheta_pos_q2
    d beta0 beta hbeta hthetaBeta


theorem wiredBeta1_nonneg_q2 (d : Nat) (beta0 : Real) (hd : 2 <= d) :
    0 <= wiredBeta1 d beta0 := by
  unfold wiredBeta1 BetaThresholdBound.beta1
  apply le_csInf (wiredThresholdSet_nonempty_q2 d beta0 hd)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig (wiredThresholdTheta d 2 beta0) n beta))
      atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat =>
        Real.log (1 / wiredSharpConstant d beta0) / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / wiredSharpConstant d beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n beta) / Real.log (n : Real)
    rw [thresholdSig_of_nonpos d n hn 2 beta0 beta hbetaNeg.le]
  change 1 <= limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d 2 beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem wiredNormalizedTheta_tendsto_betaFKTheta_div
    (d : Nat) (beta0 beta : Real) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredNormalizedTheta d 2 beta0 n beta) atTop
      (nhds (betaFKTheta d beta / wiredSharpConstant d beta0)) := by
  have h := wiredThresholdTheta_tendsto_fkTheta_div_q2 d beta0 beta hbeta
  simpa [wiredThresholdTheta, not_le.mpr hbeta,
    betaFKTheta_eq d beta hbeta] using h


theorem betaFKTheta_difference_lower_q2
    (d : Nat) (beta0 beta' beta : Real) (hd : 2 <= d)
    (hcrit : wiredBeta1 d beta0 < beta') (hbeta : beta' <= beta)
    (hupper : beta <= beta0) :
    beta - beta' <=
      betaFKTheta d beta / wiredSharpConstant d beta0 -
        betaFKTheta d beta' / wiredSharpConstant d beta0 := by
  let f := wiredNormalizedTheta d 2 beta0
  let fp := wiredNormalizedThetaPrime d 2 beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := wiredBeta1_nonneg_q2 d beta0 hd
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hbeta0pos : 0 < beta0 := hbetapos.trans_le hupper
  have hf : forall i x, x ∈ Set.Icc beta' beta ->
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => 1 / wiredSharpConstant d beta0 := by
        funext z
        simp [f, wiredNormalizedTheta, wiredOuterInnerTheta]
      rw [hconst]
      simpa [fp, wiredNormalizedThetaPrime, wiredOuterInnerThetaPrime,
        wiredOuterInnerTheta] using
        (hasDerivAt_const x (1 / wiredSharpConstant d beta0))
    · exact hasDerivAt_wiredNormalizedTheta d i
        (Nat.one_le_iff_ne_zero.mpr hi) 2 beta0 x (by norm_num)
        (hbeta'pos.trans_le hx.1)
  have hfnn : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 <= f i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_nonneg d i 2 beta0 x (by norm_num)
      (hbeta'pos.trans_le hx.1)
  have hSpos : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 < Sig i x := by
    intro i x hi hx
    exact normalizedSig_pos d i hi 2 beta0 x (by norm_num)
      (hbeta'pos.trans_le hx.1)
  have hdiff : forall i : Nat, forall x, 1 <= i -> x ∈ Set.Icc beta' beta ->
      ((i : Real) / Sig i x) * f i x <= fp i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_differential d i hi 2 x beta0 (by norm_num)
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : forall n x, 1 <= n -> x ∈ Set.Icc beta' beta ->
      Sig n beta' <= Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' <= Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        wiredNormalizedTheta_mono_beta d k 2 beta0 beta' x (by norm_num)
          hbeta'pos hx.1)
    unfold Sig
    rw [IntegrationSubcritical.isc_Sig_succ]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : forall x, x ∈ Set.Icc beta' beta ->
      Sig 1 x <= 1 / wiredSharpConstant d beta0 := by
    intro x hx
    simp [Sig, f, IntegrationSubcritical.Sig, wiredNormalizedTheta,
      wiredOuterInnerTheta]
  have hTbeta : Tendsto (fun n => Integration.meanLogTerm f n beta) atTop
      (nhds (betaFKTheta d beta / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKTheta_div d beta0 beta hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (betaFKTheta d beta' / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKTheta_div d beta0 beta' hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d 2 beta0) n beta') := by
    funext n
    symm
    exact thresholdSig_of_pos d n 2 beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_isCobounded d 2 beta0 beta' (by norm_num) hbeta0pos.le
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_bddAbove d 2 beta0 beta' (by norm_num) hbeta0pos.le
  have hm1 : 1 <= limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (wiredThresholdSet_nonempty_q2 d beta0 hd)
      (fun hab n => thresholdSig_mono_beta d n 2 beta0 (by norm_num) hab)
      (fun x n hn => thresholdSig_pos d n (by omega) 2 beta0 x (by norm_num))
      (fun x => thresholdLogRatio_isCobounded d 2 beta0 x (by norm_num) hbeta0pos.le)
      (fun x => thresholdLogRatio_bddAbove d 2 beta0 x (by norm_num) hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (betaFKTheta d beta / wiredSharpConstant d beta0)
    (betaFKTheta d beta' / wiredSharpConstant d beta0)
    (1 / wiredSharpConstant d beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1


theorem betaFKTheta_meanField_lower_q2
    (d : Nat) (beta0 beta : Real) (hd : 2 <= d)
    (hcrit : wiredBeta1 d beta0 < beta) (hupper : beta <= beta0) :
    wiredSharpConstant d beta0 * (beta - wiredBeta1 d beta0) <=
      betaFKTheta d beta := by
  have hc : 0 < wiredSharpConstant d beta0 := wiredSharpConstant_pos d beta0
  have hnormalized : beta - wiredBeta1 d beta0 <=
      betaFKTheta d beta / wiredSharpConstant d beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => betaFKTheta d x / wiredSharpConstant d beta0)
      (β₁ := wiredBeta1 d beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg (betaFKTheta_nonneg d beta') hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact betaFKTheta_difference_lower_q2 d beta0 beta' beta hd
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith


theorem wiredBeta1_le_of_betaFKTheta_pos_q2
    (d : Nat) (beta0 : Real) (hbeta0 : 0 < betaFKTheta d beta0) :
    wiredBeta1 d beta0 <= beta0 := by
  have hb0 : 0 < beta0 := by
    by_contra h
    have hz : betaFKTheta d beta0 = 0 := by
      simp only [betaFKTheta, dif_neg h]
    linarith
  have htheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta0 < 0)
        linarith : 0 < 1 - Real.exp (-beta0))
      (by linarith [Real.exp_pos (-beta0)] : 1 - Real.exp (-beta0) < 1)
      (by norm_num : (0 : Real) < 2) (q := 2) := by
    simpa only [betaFKTheta_eq d beta0 hb0] using hbeta0
  unfold wiredBeta1 BetaThresholdBound.beta1
  exact csInf_le (wiredThresholdSet_bddBelow d 2 beta0)
    (wiredThresholdSet_mem_of_fkTheta_pos_q2 d beta0 beta0 hb0 htheta)


theorem betaFKTheta_eq_zero_below_wiredBeta1_q2
    (d : Nat) (beta0 beta : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0)
    (hlt : beta < wiredBeta1 d beta0) :
    betaFKTheta d beta = 0 := by
  by_cases hbeta : 0 < beta
  · let betaMid := (beta + wiredBeta1 d beta0) / 2
    let delta := (betaMid - beta) / 2
    have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
    have hmidUpper : betaMid < wiredBeta1 d beta0 := by
      dsimp [betaMid]
      linarith
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hleft : betaMid - 2 * delta = beta := by
      dsimp [delta, betaMid]
      ring
    have hmidBeta0 : betaMid <= beta0 :=
      hmidUpper.le.trans (wiredBeta1_le_of_betaFKTheta_pos_q2 d beta0 hbeta0)
    obtain ⟨Q, hQ, hdecay⟩ :=
      wiredOuterInner_subcritical_decay_of_threshold
        d 2 delta betaMid beta0 (by norm_num) hmidBeta0 hdelta
        (by rw [hleft]; exact hbeta) (by simpa [wiredBeta1] using hmidUpper)
    have hconv : Tendsto (fun n => wiredOuterInnerTheta d 2 beta n) atTop
        (nhds (betaFKTheta d beta)) := by
      simpa only [betaFKTheta_eq d beta hbeta] using
        wiredOuterInnerTheta_tendsto_fkTheta_q2 d beta hbeta
    have hzero := BetaCMatch.bcm_expBound_tendsto_zero 1 Q delta hQ hdelta
    have hle : betaFKTheta d beta <= 0 :=
      le_of_tendsto_of_tendsto hconv hzero (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [hleft] using hdecay n hn)
    exact le_antisymm hle (betaFKTheta_nonneg d beta)
  · simp [betaFKTheta, hbeta]


theorem betaFKTheta_pos_above_wiredBeta1_q2
    (d : Nat) (beta0 beta : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0)
    (hlt : wiredBeta1 d beta0 < beta) :
    0 < betaFKTheta d beta := by
  by_cases hupper : beta <= beta0
  · have hmf := betaFKTheta_meanField_lower_q2
      d beta0 beta hd hlt hupper
    have hgap : 0 < wiredSharpConstant d beta0 *
        (beta - wiredBeta1 d beta0) := mul_pos (wiredSharpConstant_pos d beta0)
          (sub_pos.mpr hlt)
    exact hgap.trans_le hmf
  · exact hbeta0.trans_le (betaFKTheta_mono d (le_of_lt (lt_of_not_ge hupper)))


theorem betaCritical_eq_wiredBeta1_q2
    (d : Nat) (beta0 : Real) (hd : 2 <= d)
    (hbeta0 : 0 < betaFKTheta d beta0) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKTheta d)) = wiredBeta1 d beta0 := by
  exact BetaCMatch.bcm_betaC_eq_threshold (betaFKTheta d) (wiredBeta1 d beta0)
    (fun beta hlt =>
      betaFKTheta_eq_zero_below_wiredBeta1_q2 d beta0 beta hd hbeta0 hlt)
    (fun beta hlt =>
      betaFKTheta_pos_above_wiredBeta1_q2 d beta0 beta hd hbeta0 hlt)


end WiredBoxCritical
end OSSS
end StatMech
