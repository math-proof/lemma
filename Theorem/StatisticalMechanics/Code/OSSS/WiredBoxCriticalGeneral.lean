/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxCriticalGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxCritical.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.PottsCriticalCorrespondence.Part2
import Def.StatisticalMechanics.Code.OSSS.WiredBoxCriticalGeneral
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxCriticalGeneral

open Filter

open WiredBoxSharpness WiredBoxCritical

open WiredBoxLocalized

theorem betaFKThetaQ_eq
    (d : Nat) (q : Real) (hq : 1 <= q) (beta : Real) (hbeta : 0 < beta) :
    betaFKThetaQ d q hq beta = FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta < 0)
        linarith : 0 < 1 - Real.exp (-beta))
      (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
      (zero_lt_one.trans_le hq) (q := q) := by
  simp only [betaFKThetaQ, dif_pos hbeta]

theorem betaFKThetaQ_nonneg
    (d : Nat) (q : Real) (hq : 1 <= q) (beta : Real) :
    0 <= betaFKThetaQ d q hq beta := by
  by_cases hbeta : 0 < beta
  · rw [betaFKThetaQ_eq d q hq beta hbeta]
    exact FK.fkTheta_nonneg d _ _ (zero_lt_one.trans_le hq) (q := q)
  · simp [betaFKThetaQ, hbeta]


theorem wiredBeta1Q_nonneg
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q) :
    0 <= wiredBeta1Q d q beta0 := by
  unfold wiredBeta1Q BetaThresholdBound.beta1
  apply le_csInf (wiredThresholdSet_nonempty d q beta0 hd hq)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n =>
        IntegrationSubcritical.Sig (wiredThresholdTheta d q beta0) n beta))
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
        (wiredThresholdTheta d q beta0) n beta) / Real.log (n : Real)
    rw [thresholdSig_of_nonpos d n hn q beta0 beta hbetaNeg.le]
  change 1 <= limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (wiredThresholdTheta d q beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem wiredNormalizedTheta_tendsto_betaFKThetaQ_div
    (d : Nat) (q beta0 beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Tendsto (fun n => wiredNormalizedTheta d q beta0 n beta) atTop
      (nhds (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)) := by
  have h := wiredThresholdTheta_tendsto_fkTheta_div
    d q beta0 beta hq hbeta
  simpa [wiredThresholdTheta, not_le.mpr hbeta,
    betaFKThetaQ_eq d q hq beta hbeta] using h


theorem betaFKThetaQ_difference_lower
    (d : Nat) (q beta0 beta' beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hcrit : wiredBeta1Q d q beta0 < beta') (hbeta : beta' <= beta)
    (hupper : beta <= beta0) :
    beta - beta' <=
      betaFKThetaQ d q hq beta / wiredSharpConstant d beta0 -
        betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0 := by
  let f := wiredNormalizedTheta d q beta0
  let fp := wiredNormalizedThetaPrime d q beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := wiredBeta1Q_nonneg d q beta0 hd hq
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
        (Nat.one_le_iff_ne_zero.mpr hi) q beta0 x hq
        (hbeta'pos.trans_le hx.1)
  have hfnn : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 <= f i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_nonneg d i q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hSpos : forall i x, 1 <= i -> x ∈ Set.Icc beta' beta -> 0 < Sig i x := by
    intro i x hi hx
    exact normalizedSig_pos d i hi q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hdiff : forall i : Nat, forall x, 1 <= i -> x ∈ Set.Icc beta' beta ->
      ((i : Real) / Sig i x) * f i x <= fp i x := by
    intro i x hi hx
    exact wiredNormalizedTheta_differential d i hi q x beta0 hq
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : forall n x, 1 <= n -> x ∈ Set.Icc beta' beta ->
      Sig n beta' <= Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' <= Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        wiredNormalizedTheta_mono_beta d k q beta0 beta' x hq
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
      (nhds (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKThetaQ_div
        d q beta0 beta hq hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (wiredNormalizedTheta_tendsto_betaFKThetaQ_div
        d q beta0 beta' hq hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (wiredThresholdTheta d q beta0) n beta') := by
    funext n
    symm
    exact thresholdSig_of_pos d n q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_isCobounded d q beta0 beta' hq hbeta0pos.le
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact thresholdLogRatio_bddAbove d q beta0 beta' hq hbeta0pos.le
  have hm1 : 1 <= limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (wiredThresholdSet_nonempty d q beta0 hd hq)
      (fun hab n => thresholdSig_mono_beta d n q beta0 hq hab)
      (fun x n hn => thresholdSig_pos d n (by omega) q beta0 x hq)
      (fun x => thresholdLogRatio_isCobounded d q beta0 x hq hbeta0pos.le)
      (fun x => thresholdLogRatio_bddAbove d q beta0 x hq hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (betaFKThetaQ d q hq beta / wiredSharpConstant d beta0)
    (betaFKThetaQ d q hq beta' / wiredSharpConstant d beta0)
    (1 / wiredSharpConstant d beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1


theorem betaFKThetaQ_meanField_lower
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hcrit : wiredBeta1Q d q beta0 < beta) (hupper : beta <= beta0) :
    wiredSharpConstant d beta0 * (beta - wiredBeta1Q d q beta0) <=
      betaFKThetaQ d q hq beta := by
  have hc : 0 < wiredSharpConstant d beta0 := wiredSharpConstant_pos d beta0
  have hnormalized : beta - wiredBeta1Q d q beta0 <=
      betaFKThetaQ d q hq beta / wiredSharpConstant d beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => betaFKThetaQ d q hq x / wiredSharpConstant d beta0)
      (β₁ := wiredBeta1Q d q beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg (betaFKThetaQ_nonneg d q hq beta') hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact betaFKThetaQ_difference_lower d q beta0 beta' beta hd hq
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith

theorem betaFKThetaQ_mono
    (d : Nat) (q : Real) (hq : 1 <= q) : Monotone (betaFKThetaQ d q hq) := by
  intro a b hab
  by_cases hb : 0 < b
  · by_cases ha : 0 < a
    · rw [betaFKThetaQ_eq d q hq a ha, betaFKThetaQ_eq d q hq b hb]
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
      exact FK.fkgq_fkTheta_monotone_in_p hpa0 hpa1 hpb0 hpb1 hpab hq
    · rw [show betaFKThetaQ d q hq a = 0 by simp [betaFKThetaQ, ha]]
      exact betaFKThetaQ_nonneg d q hq b
  · have ha : ¬ 0 < a := fun h => hb (h.trans_le hab)
    simp [betaFKThetaQ, ha, hb]

theorem wiredBeta1Q_le_of_betaFKThetaQ_pos
    (d : Nat) (q beta0 : Real) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
    wiredBeta1Q d q beta0 <= beta0 := by
  have hb0 : 0 < beta0 := by
    by_contra h
    have hz : betaFKThetaQ d q hq beta0 = 0 := by
      simp only [betaFKThetaQ, dif_neg h]
    linarith
  have htheta : 0 < FK.fkTheta d
      (by
        have := Real.exp_lt_one_iff.mpr (by linarith : -beta0 < 0)
        linarith : 0 < 1 - Real.exp (-beta0))
      (by linarith [Real.exp_pos (-beta0)] : 1 - Real.exp (-beta0) < 1)
      (zero_lt_one.trans_le hq) (q := q) := by
    simpa only [betaFKThetaQ_eq d q hq beta0 hb0] using hbeta0
  unfold wiredBeta1Q BetaThresholdBound.beta1
  exact csInf_le (wiredThresholdSet_bddBelow d q beta0)
    (wiredThresholdSet_mem_of_fkTheta_pos d q beta0 beta0 hq hb0 htheta)

theorem betaFKThetaQ_eq_zero_below_wiredBeta1
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hlt : beta < wiredBeta1Q d q beta0) :
    betaFKThetaQ d q hq beta = 0 := by
  by_cases hbeta : 0 < beta
  · let betaMid := (beta + wiredBeta1Q d q beta0) / 2
    let delta := (betaMid - beta) / 2
    have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
    have hmidUpper : betaMid < wiredBeta1Q d q beta0 := by
      dsimp [betaMid]
      linarith
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hleft : betaMid - 2 * delta = beta := by
      dsimp [delta, betaMid]
      ring
    have hmidBeta0 : betaMid <= beta0 :=
      hmidUpper.le.trans
        (wiredBeta1Q_le_of_betaFKThetaQ_pos d q beta0 hq hbeta0)
    obtain ⟨Q, hQ, hdecay⟩ :=
      wiredOuterInner_subcritical_decay_of_threshold
        d q delta betaMid beta0 hq hmidBeta0 hdelta
        (by rw [hleft]; exact hbeta) (by simpa [wiredBeta1Q] using hmidUpper)
    have hconv : Tendsto (fun n => wiredOuterInnerTheta d q beta n) atTop
        (nhds (betaFKThetaQ d q hq beta)) := by
      simpa only [betaFKThetaQ_eq d q hq beta hbeta] using
        wiredOuterInnerTheta_tendsto_fkTheta d q beta hq hbeta
    have hzero := BetaCMatch.bcm_expBound_tendsto_zero 1 Q delta hQ hdelta
    have hle : betaFKThetaQ d q hq beta <= 0 :=
      le_of_tendsto_of_tendsto hconv hzero (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [hleft] using hdecay n hn)
    exact le_antisymm hle (betaFKThetaQ_nonneg d q hq beta)
  · simp [betaFKThetaQ, hbeta]

theorem betaFKThetaQ_pos_above_wiredBeta1
    (d : Nat) (q beta0 beta : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0)
    (hlt : wiredBeta1Q d q beta0 < beta) :
    0 < betaFKThetaQ d q hq beta := by
  by_cases hupper : beta <= beta0
  · have hmf := betaFKThetaQ_meanField_lower
      d q beta0 beta hd hq hlt hupper
    have hgap : 0 < wiredSharpConstant d beta0 *
        (beta - wiredBeta1Q d q beta0) :=
      mul_pos (wiredSharpConstant_pos d beta0) (sub_pos.mpr hlt)
    exact hgap.trans_le hmf
  · exact hbeta0.trans_le
      (betaFKThetaQ_mono d q hq (le_of_lt (lt_of_not_ge hupper)))

theorem betaCriticalQ_eq_wiredBeta1Q
    (d : Nat) (q beta0 : Real) (hd : 2 <= d) (hq : 1 <= q)
    (hbeta0 : 0 < betaFKThetaQ d q hq beta0) :
    sSup (BetaCMatch.bcm_subcriticalSet (betaFKThetaQ d q hq)) =
      wiredBeta1Q d q beta0 := by
  exact BetaCMatch.bcm_betaC_eq_threshold
    (betaFKThetaQ d q hq) (wiredBeta1Q d q beta0)
    (fun beta hlt => betaFKThetaQ_eq_zero_below_wiredBeta1
      d q beta0 beta hd hq hbeta0 hlt)
    (fun beta hlt => betaFKThetaQ_pos_above_wiredBeta1
      d q beta0 beta hd hq hbeta0 hlt)

end WiredBoxCriticalGeneral
end OSSS
end StatMech
