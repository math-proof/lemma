/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part6
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularCriticalBeta_pos
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 < triangularCriticalBeta q := by
  unfold triangularCriticalBeta
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc.2) (by linarith [hpc.1]))

theorem triangularCriticalBeta_param
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    1 - Real.exp (-triangularCriticalBeta q) = triangular.criticalPoint q := by
  unfold triangularCriticalBeta
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc.2)]
  ring

theorem betaToP_lt_triangularCritical_of_lt
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : beta < triangularCriticalBeta q) :
    1 - Real.exp (-beta) < triangular.criticalPoint q := by
  rw [← triangularCriticalBeta_param q hpc]
  have hexp : Real.exp (-triangularCriticalBeta q) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem triangularCritical_lt_betaToP_of_lt
    (q : Real) (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : triangularCriticalBeta q < beta) :
    triangular.criticalPoint q < 1 - Real.exp (-beta) := by
  rw [← triangularCriticalBeta_param q hpc]
  have hexp : Real.exp (-beta) < Real.exp (-triangularCriticalBeta q) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem triangularNormalizedTheta_tendsto_percolation_div
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => triangularNormalizedTheta q beta0 n beta) atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / triangularSharpConstant beta0)) := by
  simpa [triangularNormalizedTheta] using
    (triangularOuterInnerTheta_tendsto_percolation q beta hq hbeta).div_const
      (triangularSharpConstant beta0)

theorem triangularThresholdSet_mem_of_percolation_pos
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hperc : 0 < triangular.wiredPercolationProbability
      (1 - Real.exp (-beta)) q) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (triangularThresholdTheta q beta0) n b) := by
  let L := triangular.wiredPercolationProbability
    (1 - Real.exp (-beta)) q / triangularSharpConstant beta0
  have hL : 0 < L := div_pos hperc (triangularSharpConstant_pos beta0)
  have hconv : Tendsto
      (fun n => triangularThresholdTheta q beta0 n beta) atTop (nhds L) := by
    simpa [L, triangularThresholdTheta, not_le.mpr hbeta] using
      triangularNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)) atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]

theorem triangularThresholdSet_nonempty
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n b)).Nonempty := by
  let beta := triangularCriticalBeta q + 1
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith [triangularCriticalBeta_pos q hpc]
  have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
    constructor
    · rw [sub_pos]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    · linarith [Real.exp_pos (-beta)]
  have hsuper : triangular.criticalPoint q < 1 - Real.exp (-beta) :=
    triangularCritical_lt_betaToP_of_lt q hpc (by simp [beta])
  have hsharp := triangular.offCriticalSharpness hq hpc
  have hperc : 0 < triangular.wiredPercolationProbability
      (1 - Real.exp (-beta)) q := hsharp.2 _ hp hsuper
  exact ⟨beta, triangularThresholdSet_mem_of_percolation_pos
    q beta0 beta hq hbeta hperc⟩

theorem triangularBeta1_nonneg
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 ≤ triangularBeta1 q beta0 := by
  unfold triangularBeta1 BetaThresholdBound.beta1
  apply le_csInf (triangularThresholdSet_nonempty q beta0 hq hpc)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta)) atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat =>
        Real.log (1 / triangularSharpConstant beta0) / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / triangularSharpConstant beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta) / Real.log (n : Real)
    rw [triangularThresholdSig_of_nonpos n hn q beta0 beta hbetaNeg.le]
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem triangularThresholdLogRatio_bddAbove
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta)) := by
  exact BetaThresholdBound.btb_bddAbove_ratio_of_linear
    (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta)
    (1 / triangularSharpConstant beta0)
    (one_le_inv_triangularSharpConstant beta0 hbeta0)
    (fun n hn => triangularThresholdSig_pos n (by omega) q beta0 beta hq)
    (fun n => triangularThresholdSig_le_linear n q beta0 beta hq)

theorem triangularThresholdLogRatio_cobounded
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta)) := by
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta))
    (x := 0) atTop ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig1 : 1 ≤ IntegrationSubcritical.Sig
      (triangularThresholdTheta q beta0) n beta := by
    have hzero : 1 ≤ triangularThresholdTheta q beta0 0 beta := by
      have hM := one_le_inv_triangularSharpConstant beta0 hbeta0
      by_cases hbeta : beta ≤ 0
      · simpa [triangularThresholdTheta, hbeta] using hM
      · rw [triangularThresholdTheta_of_pos 0 q beta0 beta (lt_of_not_ge hbeta)]
        simpa [triangularNormalizedTheta, triangularOuterInnerTheta] using hM
    exact hzero.trans (by
      unfold IntegrationSubcritical.Sig
      apply Finset.single_le_sum
        (fun k _ => triangularThresholdTheta_nonneg k q beta0 beta hq)
      exact Finset.mem_range.mpr (by omega))
  unfold BetaThresholdBound.logRatio
  exact div_nonneg (Real.log_nonneg hsig1) hlogn.le


theorem triangularPercolation_difference_lower
    (q beta0 beta' beta : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : triangularBeta1 q beta0 < beta') (hbeta : beta' ≤ beta)
    (hupper : beta ≤ beta0) :
    beta - beta' ≤
      triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q /
          triangularSharpConstant beta0 -
        triangular.wiredPercolationProbability (1 - Real.exp (-beta')) q /
          triangularSharpConstant beta0 := by
  let f := triangularNormalizedTheta q beta0
  let fp := triangularNormalizedThetaPrime q beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := triangularBeta1_nonneg q beta0 hq hpc
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hbeta0pos : 0 < beta0 := hbetapos.trans_le hupper
  have hf : ∀ i x, x ∈ Set.Icc beta' beta →
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => 1 / triangularSharpConstant beta0 := by
        funext z
        simp [f, triangularNormalizedTheta, triangularOuterInnerTheta]
      rw [hconst]
      simpa [fp, triangularNormalizedThetaPrime,
        triangularOuterInnerThetaPrime, triangularOuterInnerTheta] using
        (hasDerivAt_const x (1 / triangularSharpConstant beta0))
    · exact hasDerivAt_triangularNormalizedTheta i
        (Nat.one_le_iff_ne_zero.mpr hi) q beta0 x hq
        (hbeta'pos.trans_le hx.1)
  have hfnn : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 ≤ f i x := by
    intro i x hi hx
    exact triangularNormalizedTheta_nonneg i q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hSpos : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 < Sig i x := by
    intro i x hi hx
    exact triangularNormalizedSig_pos i hi q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hdiff : ∀ i : Nat, ∀ x, 1 ≤ i → x ∈ Set.Icc beta' beta →
      ((i : Real) / Sig i x) * f i x ≤ fp i x := by
    intro i x hi hx
    exact triangularNormalizedTheta_differential i hi q x beta0 hq
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : ∀ n x, 1 ≤ n → x ∈ Set.Icc beta' beta →
      Sig n beta' ≤ Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' ≤ Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        triangularNormalizedTheta_mono_beta k q beta0 beta' x hq
          hbeta'pos hx.1)
    unfold Sig
    rw [IntegrationSubcritical.isc_Sig_succ]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : ∀ x, x ∈ Set.Icc beta' beta →
      Sig 1 x ≤ 1 / triangularSharpConstant beta0 := by
    intro x hx
    simp [Sig, f, IntegrationSubcritical.Sig, triangularNormalizedTheta,
      triangularOuterInnerTheta]
  have hTbeta : Tendsto (fun n => Integration.meanLogTerm f n beta) atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / triangularSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (triangularNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (triangular.wiredPercolationProbability
        (1 - Real.exp (-beta')) q / triangularSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (triangularNormalizedTheta_tendsto_percolation_div
        q beta0 beta' hq hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (triangularThresholdTheta q beta0) n beta') := by
    funext n
    symm
    exact triangularThresholdSig_of_pos n q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact triangularThresholdLogRatio_cobounded
      q beta0 beta' hq hbeta0pos.le
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact triangularThresholdLogRatio_bddAbove
      q beta0 beta' hq hbeta0pos.le
  have hm1 : 1 ≤ Filter.limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (triangularThresholdSet_nonempty q beta0 hq hpc)
      (fun hab n => triangularThresholdSig_mono_beta n q beta0 hq hab)
      (fun x n hn => triangularThresholdSig_pos n (by omega) q beta0 x hq)
      (fun x => triangularThresholdLogRatio_cobounded
        q beta0 x hq hbeta0pos.le)
      (fun x => triangularThresholdLogRatio_bddAbove
        q beta0 x hq hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q /
      triangularSharpConstant beta0)
    (triangular.wiredPercolationProbability (1 - Real.exp (-beta')) q /
      triangularSharpConstant beta0)
    (1 / triangularSharpConstant beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1

theorem triangularPercolation_meanField_lower
    (q beta0 beta : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : triangularBeta1 q beta0 < beta) (hupper : beta ≤ beta0) :
    triangularSharpConstant beta0 * (beta - triangularBeta1 q beta0) ≤
      triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q := by
  have hc := triangularSharpConstant_pos beta0
  have hnormalized : beta - triangularBeta1 q beta0 ≤
      triangular.wiredPercolationProbability (1 - Real.exp (-beta)) q /
        triangularSharpConstant beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => triangular.wiredPercolationProbability
        (1 - Real.exp (-x)) q / triangularSharpConstant beta0)
      (β₁ := triangularBeta1 q beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg
        (triangular.wiredPercolationProbability_nonneg _ _) hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact triangularPercolation_difference_lower q beta0 beta' beta hq hpc
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith


theorem triangularBeta1_eq_criticalBeta_of_ge
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta0 : triangularCriticalBeta q ≤ beta0) :
    triangularBeta1 q beta0 = triangularCriticalBeta q := by
  let betaC := triangularCriticalBeta q
  let Sgf : Real → Nat → Real := fun b n => IntegrationSubcritical.Sig
    (triangularThresholdTheta q beta0) n b
  have hbetaCpos : 0 < betaC := triangularCriticalBeta_pos q hpc
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using triangularThresholdSet_bddBelow q beta0
  have hsharp := triangular.offCriticalSharpness hq hpc
  have hle : triangularBeta1 q beta0 ≤ betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hpcp : triangular.criticalPoint q < 1 - Real.exp (-beta) :=
      triangularCritical_lt_betaToP_of_lt q hpc hbetaCbeta
    have hperc : 0 < triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := hsharp.2 _ hp hpcp
    have hmem := triangularThresholdSet_mem_of_percolation_pos
      q beta0 beta hq hbetapos hperc
    unfold triangularBeta1 BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC ≤ triangularBeta1 q beta0 := by
    by_contra hnot
    have hlt : triangularBeta1 q beta0 < betaC := lt_of_not_ge hnot
    let beta := (triangularBeta1 q beta0 + betaC) / 2
    have hcrit : triangularBeta1 q beta0 < beta := by
      dsimp [beta]
      linarith
    have hbetaC : beta < betaC := by
      dsimp [beta]
      linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (triangularBeta1_nonneg q beta0 hq hpc) hcrit
    have hmean := triangularPercolation_meanField_lower
      q beta0 beta hq hpc hcrit (hbetaC.le.trans hbeta0)
    have hpercPos : 0 < triangular.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := by
      have hc := triangularSharpConstant_pos beta0
      have hgap : 0 < beta - triangularBeta1 q beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hppc : 1 - Real.exp (-beta) < triangular.criticalPoint q :=
      betaToP_lt_triangularCritical_of_lt q hpc hbetaC
    have hnotperc := hsharp.1 _ hp hppc
    exact hnotperc hpercPos
  exact le_antisymm hle hge


theorem triangularOuterInner_exponential_decay_below_critical
    (q beta : Real) (hq : 1 ≤ q)
    (hpc : triangular.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta : 0 < beta) (hsub : beta < triangularCriticalBeta q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 ≤ n →
      triangularOuterInnerTheta q beta n ≤
        Real.exp (-((n : Real) / Q *
          ((triangularCriticalBeta q - beta) / 4))) := by
  let betaC := triangularCriticalBeta q
  let betaMid := (beta + betaC) / 2
  let delta := (betaC - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta, betaC]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidLe : betaMid ≤ betaC := by dsimp [betaMid]; linarith
  have hthreshold : triangularBeta1 q betaC = betaC :=
    triangularBeta1_eq_criticalBeta_of_ge q betaC hq hpc le_rfl
  have hmidThreshold : betaMid < triangularBeta1 q betaC := by
    rw [hthreshold]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    triangularOuterInner_subcritical_decay_of_threshold
      q delta betaMid betaC hq hmidLe hdelta
      (by rw [hleft]; exact hbeta)
      (by simpa [triangularBeta1] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, betaC, mul_assoc] using hdecay n hn

end StatMech.FK.PeriodicPlanar
