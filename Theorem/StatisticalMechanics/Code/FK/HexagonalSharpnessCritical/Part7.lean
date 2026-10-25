/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part7
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalCriticalBeta_pos
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 < hexagonalCriticalBeta q := by
  unfold hexagonalCriticalBeta
  exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hpc.2) (by linarith [hpc.1]))

theorem hexagonalCriticalBeta_param
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    1 - Real.exp (-hexagonalCriticalBeta q) = hexagonal.criticalPoint q := by
  unfold hexagonalCriticalBeta
  rw [neg_neg, Real.exp_log (sub_pos.mpr hpc.2)]
  ring

theorem betaToP_lt_hexagonalCritical_of_lt
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : beta < hexagonalCriticalBeta q) :
    1 - Real.exp (-beta) < hexagonal.criticalPoint q := by
  rw [← hexagonalCriticalBeta_param q hpc]
  have hexp : Real.exp (-hexagonalCriticalBeta q) < Real.exp (-beta) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem hexagonalCritical_lt_betaToP_of_lt
    (q : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    {beta : Real} (hbeta : hexagonalCriticalBeta q < beta) :
    hexagonal.criticalPoint q < 1 - Real.exp (-beta) := by
  rw [← hexagonalCriticalBeta_param q hpc]
  have hexp : Real.exp (-beta) < Real.exp (-hexagonalCriticalBeta q) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem hexagonalNormalizedTheta_tendsto_percolation_div
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    Tendsto (fun n => hexagonalNormalizedTheta q beta0 n beta) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0)) := by
  simpa [hexagonalNormalizedTheta] using
    (hexagonalOuterInnerTheta_tendsto_percolation q beta hq hbeta).div_const
      (hexagonalSharpConstant beta0)

theorem hexagonalThresholdSet_mem_of_percolation_pos
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta)
    (hperc : 0 < hexagonal.wiredPercolationProbability
      (1 - Real.exp (-beta)) q) :
    beta ∈ BetaThresholdBound.thresholdSet (fun b n =>
      IntegrationSubcritical.Sig (hexagonalThresholdTheta q beta0) n b) := by
  let L := hexagonal.wiredPercolationProbability
    (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0
  have hL : 0 < L := div_pos hperc (hexagonalSharpConstant_pos beta0)
  have hconv : Tendsto
      (fun n => hexagonalThresholdTheta q beta0 n beta) atTop (nhds L) := by
    simpa [L, hexagonalThresholdTheta, not_le.mpr hbeta] using
      hexagonalNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbeta
  have hratio := LogCesaroLimit.logRatio_partialSum_tendsto_one hconv hL
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)) atTop
  unfold IntegrationSubcritical.Sig
  rw [hratio.limsup_eq]

theorem hexagonalThresholdSet_nonempty
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    (BetaThresholdBound.thresholdSet (fun b n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n b)).Nonempty := by
  let beta := hexagonalCriticalBeta q + 1
  have hbeta : 0 < beta := by
    dsimp [beta]
    linarith [hexagonalCriticalBeta_pos q hpc]
  have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
    constructor
    · rw [sub_pos]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    · linarith [Real.exp_pos (-beta)]
  have hsuper : hexagonal.criticalPoint q < 1 - Real.exp (-beta) :=
    hexagonalCritical_lt_betaToP_of_lt q hpc (by simp [beta])
  have hsharp := hexagonal.offCriticalSharpness hq hpc
  have hperc : 0 < hexagonal.wiredPercolationProbability
      (1 - Real.exp (-beta)) q := hsharp.2 _ hp hsuper
  exact ⟨beta, hexagonalThresholdSet_mem_of_percolation_pos
    q beta0 beta hq hbeta hperc⟩

theorem hexagonalBeta1_nonneg
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    0 ≤ hexagonalBeta1 q beta0 := by
  unfold hexagonalBeta1 BetaThresholdBound.beta1
  apply le_csInf (hexagonalThresholdSet_nonempty q beta0 hq hpc)
  intro beta hmem
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  have htend : Tendsto
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta)) atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat =>
        Real.log (1 / hexagonalSharpConstant beta0) / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold BetaThresholdBound.logRatio
    change Real.log (1 / hexagonalSharpConstant beta0) / Real.log (n : Real) =
      Real.log (IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta) / Real.log (n : Real)
    rw [hexagonalThresholdSig_of_nonpos n hn q beta0 beta hbetaNeg.le]
  change 1 ≤ Filter.limsup
    (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)) atTop at hmem
  rw [htend.limsup_eq] at hmem
  linarith

theorem hexagonalThresholdLogRatio_bddAbove
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta)) := by
  exact BetaThresholdBound.btb_bddAbove_ratio_of_linear
    (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta)
    (1 / hexagonalSharpConstant beta0)
    (one_le_inv_hexagonalSharpConstant beta0 hbeta0)
    (fun n hn => hexagonalThresholdSig_pos n (by omega) q beta0 beta hq)
    (fun n => hexagonalThresholdSig_le_linear n q beta0 beta hq)

theorem hexagonalThresholdLogRatio_cobounded
    (q beta0 beta : Real) (hq : 1 ≤ q) (hbeta0 : 0 ≤ beta0) :
    IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta)) := by
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := BetaThresholdBound.logRatio (fun n => IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta))
    (x := 0) atTop ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig1 : 1 ≤ IntegrationSubcritical.Sig
      (hexagonalThresholdTheta q beta0) n beta := by
    have hzero : 1 ≤ hexagonalThresholdTheta q beta0 0 beta := by
      have hM := one_le_inv_hexagonalSharpConstant beta0 hbeta0
      by_cases hbeta : beta ≤ 0
      · simpa [hexagonalThresholdTheta, hbeta] using hM
      · rw [hexagonalThresholdTheta_of_pos 0 q beta0 beta (lt_of_not_ge hbeta)]
        simpa [hexagonalNormalizedTheta, hexagonalOuterInnerTheta] using hM
    exact hzero.trans (by
      unfold IntegrationSubcritical.Sig
      apply Finset.single_le_sum
        (fun k _ => hexagonalThresholdTheta_nonneg k q beta0 beta hq)
      exact Finset.mem_range.mpr (by omega))
  unfold BetaThresholdBound.logRatio
  exact div_nonneg (Real.log_nonneg hsig1) hlogn.le


theorem hexagonalPercolation_difference_lower
    (q beta0 beta' beta : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : hexagonalBeta1 q beta0 < beta') (hbeta : beta' ≤ beta)
    (hupper : beta ≤ beta0) :
    beta - beta' ≤
      hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q /
          hexagonalSharpConstant beta0 -
        hexagonal.wiredPercolationProbability (1 - Real.exp (-beta')) q /
          hexagonalSharpConstant beta0 := by
  let f := hexagonalNormalizedTheta q beta0
  let fp := hexagonalNormalizedThetaPrime q beta0
  let Sig := IntegrationSubcritical.Sig f
  have hbeta1nn := hexagonalBeta1_nonneg q beta0 hq hpc
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hbeta0pos : 0 < beta0 := hbetapos.trans_le hupper
  have hf : ∀ i x, x ∈ Set.Icc beta' beta →
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => 1 / hexagonalSharpConstant beta0 := by
        funext z
        simp [f, hexagonalNormalizedTheta, hexagonalOuterInnerTheta]
      rw [hconst]
      simpa [fp, hexagonalNormalizedThetaPrime,
        hexagonalOuterInnerThetaPrime, hexagonalOuterInnerTheta] using
        (hasDerivAt_const x (1 / hexagonalSharpConstant beta0))
    · exact hasDerivAt_hexagonalNormalizedTheta i
        (Nat.one_le_iff_ne_zero.mpr hi) q beta0 x hq
        (hbeta'pos.trans_le hx.1)
  have hfnn : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 ≤ f i x := by
    intro i x hi hx
    exact hexagonalNormalizedTheta_nonneg i q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hSpos : ∀ i x, 1 ≤ i → x ∈ Set.Icc beta' beta → 0 < Sig i x := by
    intro i x hi hx
    exact hexagonalNormalizedSig_pos i hi q beta0 x hq
      (hbeta'pos.trans_le hx.1)
  have hdiff : ∀ i : Nat, ∀ x, 1 ≤ i → x ∈ Set.Icc beta' beta →
      ((i : Real) / Sig i x) * f i x ≤ fp i x := by
    intro i x hi hx
    exact hexagonalNormalizedTheta_differential i hi q x beta0 hq
      (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : ∀ n x, 1 ≤ n → x ∈ Set.Icc beta' beta →
      Sig n beta' ≤ Sig (n + 1) x := by
    intro n x hn hx
    have hmono : Sig n beta' ≤ Sig n x :=
      IntegrationSubcritical.isc_Sig_mono f n hx.1 (fun k =>
        hexagonalNormalizedTheta_mono_beta k q beta0 beta' x hq
          hbeta'pos hx.1)
    unfold Sig
    rw [IntegrationSubcritical.isc_Sig_succ]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : ∀ x, x ∈ Set.Icc beta' beta →
      Sig 1 x ≤ 1 / hexagonalSharpConstant beta0 := by
    intro x hx
    simp [Sig, f, IntegrationSubcritical.Sig, hexagonalNormalizedTheta,
      hexagonalOuterInnerTheta]
  have hTbeta : Tendsto (fun n => Integration.meanLogTerm f n beta) atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q / hexagonalSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (hexagonalNormalizedTheta_tendsto_percolation_div
        q beta0 beta hq hbetapos)
  have hTbeta' : Tendsto (fun n => Integration.meanLogTerm f n beta') atTop
      (nhds (hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta')) q / hexagonalSharpConstant beta0)) :=
    LogCesaroLimit.meanLogTerm_tendsto
      (hexagonalNormalizedTheta_tendsto_percolation_div
        q beta0 beta' hq hbeta'pos)
  have hSigEq : (fun n => Sig n beta') =
      (fun n => IntegrationSubcritical.Sig
        (hexagonalThresholdTheta q beta0) n beta') := by
    funext n
    symm
    exact hexagonalThresholdSig_of_pos n q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact hexagonalThresholdLogRatio_cobounded
      q beta0 beta' hq hbeta0pos.le
  have hbdd : IsBoundedUnder (· ≤ ·) atTop
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) := by
    rw [hSigEq]
    exact hexagonalThresholdLogRatio_bddAbove
      q beta0 beta' hq hbeta0pos.le
  have hm1 : 1 ≤ Filter.limsup
      (BetaThresholdBound.logRatio (fun n => Sig n beta')) atTop := by
    rw [hSigEq]
    exact LogCesaroLimit.one_le_limsup_of_beta1_lt
      (hexagonalThresholdSet_nonempty q beta0 hq hpc)
      (fun hab n => hexagonalThresholdSig_mono_beta n q beta0 hq hab)
      (fun x n hn => hexagonalThresholdSig_pos n (by omega) q beta0 x hq)
      (fun x => hexagonalThresholdLogRatio_cobounded
        q beta0 x hq hbeta0pos.le)
      (fun x => hexagonalThresholdLogRatio_bddAbove
        q beta0 x hq hbeta0pos.le)
      hcrit
  exact LogCesaroLimit.meanField_lower_of_threshold_rate
    f fp Sig beta' beta
    (hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q /
      hexagonalSharpConstant beta0)
    (hexagonal.wiredPercolationProbability (1 - Real.exp (-beta')) q /
      hexagonalSharpConstant beta0)
    (1 / hexagonalSharpConstant beta0) hbeta hf
    (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff hSmono hS1le
    hTbeta hTbeta' hcob hbdd hm1

theorem hexagonalPercolation_meanField_lower
    (q beta0 beta : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hcrit : hexagonalBeta1 q beta0 < beta) (hupper : beta ≤ beta0) :
    hexagonalSharpConstant beta0 * (beta - hexagonalBeta1 q beta0) ≤
      hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q := by
  have hc := hexagonalSharpConstant_pos beta0
  have hnormalized : beta - hexagonalBeta1 q beta0 ≤
      hexagonal.wiredPercolationProbability (1 - Real.exp (-beta)) q /
        hexagonalSharpConstant beta0 := by
    apply LogCesaroLimit.meanField_lower_at_threshold
      (f := fun x => hexagonal.wiredPercolationProbability
        (1 - Real.exp (-x)) q / hexagonalSharpConstant beta0)
      (β₁ := hexagonalBeta1 q beta0) (β := beta) hcrit
    · intro beta' hbeta'1 hbeta'beta
      exact div_nonneg
        (hexagonal.wiredPercolationProbability_nonneg _ _) hc.le
    · intro beta' hbeta'1 hbeta'beta
      exact hexagonalPercolation_difference_lower q beta0 beta' beta hq hpc
        hbeta'1 hbeta'beta.le hupper
  have := (le_div_iff₀ hc).mp hnormalized
  nlinarith


theorem hexagonalBeta1_eq_criticalBeta_of_ge
    (q beta0 : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta0 : hexagonalCriticalBeta q ≤ beta0) :
    hexagonalBeta1 q beta0 = hexagonalCriticalBeta q := by
  let betaC := hexagonalCriticalBeta q
  let Sgf : Real → Nat → Real := fun b n => IntegrationSubcritical.Sig
    (hexagonalThresholdTheta q beta0) n b
  have hbetaCpos : 0 < betaC := hexagonalCriticalBeta_pos q hpc
  have hbdd : BddBelow (BetaThresholdBound.thresholdSet Sgf) := by
    simpa [Sgf] using hexagonalThresholdSet_bddBelow q beta0
  have hsharp := hexagonal.offCriticalSharpness hq hpc
  have hle : hexagonalBeta1 q beta0 ≤ betaC := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro beta hbetaCbeta
    have hbetapos : 0 < beta := hbetaCpos.trans hbetaCbeta
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hpcp : hexagonal.criticalPoint q < 1 - Real.exp (-beta) :=
      hexagonalCritical_lt_betaToP_of_lt q hpc hbetaCbeta
    have hperc : 0 < hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := hsharp.2 _ hp hpcp
    have hmem := hexagonalThresholdSet_mem_of_percolation_pos
      q beta0 beta hq hbetapos hperc
    unfold hexagonalBeta1 BetaThresholdBound.beta1
    exact csInf_le hbdd (by simpa [Sgf] using hmem)
  have hge : betaC ≤ hexagonalBeta1 q beta0 := by
    by_contra hnot
    have hlt : hexagonalBeta1 q beta0 < betaC := lt_of_not_ge hnot
    let beta := (hexagonalBeta1 q beta0 + betaC) / 2
    have hcrit : hexagonalBeta1 q beta0 < beta := by
      dsimp [beta]
      linarith
    have hbetaC : beta < betaC := by
      dsimp [beta]
      linarith
    have hbetapos : 0 < beta :=
      lt_of_le_of_lt (hexagonalBeta1_nonneg q beta0 hq hpc) hcrit
    have hmean := hexagonalPercolation_meanField_lower
      q beta0 beta hq hpc hcrit (hbetaC.le.trans hbeta0)
    have hpercPos : 0 < hexagonal.wiredPercolationProbability
        (1 - Real.exp (-beta)) q := by
      have hc := hexagonalSharpConstant_pos beta0
      have hgap : 0 < beta - hexagonalBeta1 q beta0 := sub_pos.mpr hcrit
      nlinarith
    have hp : 1 - Real.exp (-beta) ∈ Set.Ioo (0 : Real) 1 := by
      constructor
      · rw [sub_pos]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      · linarith [Real.exp_pos (-beta)]
    have hppc : 1 - Real.exp (-beta) < hexagonal.criticalPoint q :=
      betaToP_lt_hexagonalCritical_of_lt q hpc hbetaC
    have hnotperc := hsharp.1 _ hp hppc
    exact hnotperc hpercPos
  exact le_antisymm hle hge


theorem hexagonalOuterInner_exponential_decay_below_critical
    (q beta : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hbeta : 0 < beta) (hsub : beta < hexagonalCriticalBeta q) :
    ∃ Q : Real, 0 < Q ∧ ∀ n : Nat, 1 ≤ n →
      hexagonalOuterInnerTheta q beta n ≤
        Real.exp (-((n : Real) / Q *
          ((hexagonalCriticalBeta q - beta) / 4))) := by
  let betaC := hexagonalCriticalBeta q
  let betaMid := (beta + betaC) / 2
  let delta := (betaC - beta) / 4
  have hdelta : 0 < delta := by dsimp [delta, betaC]; linarith
  have hleft : betaMid - 2 * delta = beta := by
    dsimp [betaMid, delta]
    ring
  have hmidLe : betaMid ≤ betaC := by dsimp [betaMid]; linarith
  have hthreshold : hexagonalBeta1 q betaC = betaC :=
    hexagonalBeta1_eq_criticalBeta_of_ge q betaC hq hpc le_rfl
  have hmidThreshold : betaMid < hexagonalBeta1 q betaC := by
    rw [hthreshold]
    dsimp [betaMid]
    linarith
  obtain ⟨Q, hQ, hdecay⟩ :=
    hexagonalOuterInner_subcritical_decay_of_threshold
      q delta betaMid betaC hq hmidLe hdelta
      (by rw [hleft]; exact hbeta)
      (by simpa [hexagonalBeta1] using hmidThreshold)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  simpa [hleft, delta, betaC, mul_assoc] using hdecay n hn


theorem hexagonal_wiredTwoPointProbability_le_theta
    (k : Nat) (hk : 1 ≤ k) (x y : HexVertex)
    (hxy : k ≤ centeredRadius x.1 y.1) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    hexagonal.wiredTwoPointProbability (1 - Real.exp (-beta)) q x y ≤
      hexagonalOuterInnerTheta q beta k := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  let mu := hexagonal.wiredBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq)
  have hmono : (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
      (hexagonal.twoPointEvent x y) ≤
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (hexagonalTransBufferLevel k x.1)
          (hexagonalBufferedTransShellEvent k x)) :=
    measureReal_mono (hexagonal_twoPointEvent_subset_transShell k hk x y hxy)
      (measure_ne_top _ _)
  rw [show hexagonal.wiredTwoPointProbability
      (1 - Real.exp (-beta)) q x y =
      (mu : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.twoPointEvent x y) by
    simp [PeriodicGraph.wiredTwoPointProbability, hp, hp1,
      zero_lt_one.trans_le hq, mu]]
  exact hmono.trans
    (hexagonalBufferedTransShell_infinite_le_theta
      k hk x q beta hq hbeta)

theorem hexagonalBetaOfP_pos {p : Real} (hp : 0 < p) (hp1 : p < 1) :
    0 < -Real.log (1 - p) :=
  neg_pos.mpr (Real.log_neg (sub_pos.mpr hp1) (by linarith))

theorem hexagonalBetaOfP_param {p : Real} (hp1 : p < 1) :
    1 - Real.exp (-(-Real.log (1 - p))) = p := by
  rw [neg_neg, Real.exp_log (sub_pos.mpr hp1)]
  ring

theorem hexagonalBetaOfP_lt_criticalBeta
    (q p : Real) (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1)
    (hp1 : p < 1) (hsub : p < hexagonal.criticalPoint q) :
    -Real.log (1 - p) < hexagonalCriticalBeta q := by
  by_contra hnot
  have hle : hexagonalCriticalBeta q ≤ -Real.log (1 - p) :=
    le_of_not_gt hnot
  have hexp : Real.exp (-(-Real.log (1 - p))) ≤
      Real.exp (-hexagonalCriticalBeta q) :=
    Real.exp_le_exp.mpr (neg_le_neg hle)
  have hpEq := hexagonalBetaOfP_param hp1
  have hcEq := hexagonalCriticalBeta_param q hpc
  linarith

theorem hexagonal_centeredRadius_eq_zero_iff (x y : Site 2) :
    centeredRadius x y = 0 ↔ x = y := by
  constructor
  · intro h
    apply funext
    intro i
    have hle : centeredRadius x y ≤ 0 := h.le
    rw [centeredRadius, siteRadius_le_iff] at hle
    have hi := hle i
    simp only at hi
    have : y i - x i = 0 := Int.natAbs_eq_zero.mp (Nat.le_zero.mp hi)
    linarith
  · rintro rfl
    exact centeredRadius_self x

theorem hexToTriAnchor_sub_mem_box_add_two
    {x y : HexVertex} {r : Nat} (hxy : y.1 - x.1 ∈ box 2 r) :
    hexToTriAnchor y - hexToTriAnchor x ∈ box 2 (r + 2) := by
  have hx : x.1 - hexToTriAnchor x ∈ box 2 1 := by
    rcases x with ⟨x, bx⟩
    cases bx with
    | false => simp [hexToTriAnchor]
    | true =>
        have hx0 : Matrix.vecHead x = x 0 := rfl
        have hx1 : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
        intro i
        fin_cases i <;>
          simp [hexToTriAnchor, hexagonalStep, Matrix.cons_val_zero,
            Matrix.cons_val_one, hx0, hx1]
  have hy : hexToTriAnchor y - y.1 ∈ box 2 1 := by
    rcases y with ⟨y, cy⟩
    cases cy with
    | false => simp [hexToTriAnchor]
    | true =>
        have hy0 : Matrix.vecHead y = y 0 := rfl
        have hy1 : Matrix.vecHead (Matrix.vecTail y) = y 1 := rfl
        intro i
        fin_cases i <;>
          simp [hexToTriAnchor, hexagonalStep, Matrix.cons_val_zero,
            Matrix.cons_val_one, hy0, hy1]
  intro i
  have hxi := hx i
  have hxyi := hxy i
  have hyi := hy i
  change (x.1 i - hexToTriAnchor x i).natAbs ≤ 1 at hxi
  change (y.1 i - x.1 i).natAbs ≤ r at hxyi
  change (hexToTriAnchor y i - y.1 i).natAbs ≤ 1 at hyi
  change (hexToTriAnchor y i - hexToTriAnchor x i).natAbs ≤ r + 2
  calc
    (hexToTriAnchor y i - hexToTriAnchor x i).natAbs =
        ((hexToTriAnchor y i - y.1 i) +
          ((y.1 i - x.1 i) + (x.1 i - hexToTriAnchor x i))).natAbs := by
      congr 1
      ring
    _ ≤ (hexToTriAnchor y i - y.1 i).natAbs +
        ((y.1 i - x.1 i) + (x.1 i - hexToTriAnchor x i)).natAbs :=
      Int.natAbs_add_le _ _
    _ ≤ (hexToTriAnchor y i - y.1 i).natAbs +
        ((y.1 i - x.1 i).natAbs +
          (x.1 i - hexToTriAnchor x i).natAbs) := by
      gcongr
      exact Int.natAbs_add_le _ _
    _ ≤ 1 + (r + 1) := Nat.add_le_add hyi (Nat.add_le_add hxyi hxi)
    _ = r + 2 := by omega


theorem hexagonal_subcritical_twoPoint_exponential_decay
    (q : Real) (hq : 1 ≤ q)
    (hpc : hexagonal.criticalPoint q ∈ Set.Ioo (0 : Real) 1) :
    SubcriticalTwoPointExponentialDecay
      hexagonal q (hexagonal.criticalPoint q) := by
  intro p hp
  have hp1 : p < 1 := hp.2.trans hpc.2
  let beta := -Real.log (1 - p)
  have hbeta : 0 < beta := hexagonalBetaOfP_pos hp.1 hp1
  have hsub : beta < hexagonalCriticalBeta q :=
    hexagonalBetaOfP_lt_criticalBeta q p hpc hp1 hp.2
  obtain ⟨Q, hQ, hdecay⟩ :=
    hexagonalOuterInner_exponential_decay_below_critical
      q beta hq hpc hbeta hsub
  let delta := (hexagonalCriticalBeta q - beta) / 4
  let c := delta / (4 * Q)
  let C := Real.exp (10 * c)
  refine ⟨c, C, ?_, Real.exp_pos _, ?_⟩
  · have hdelta : 0 < delta := by dsimp [delta]; linarith
    dsimp [c]
    positivity
  intro x y
  let r := centeredRadius x.1 y.1
  have hpEq : 1 - Real.exp (-beta) = p := by
    dsimp [beta]
    exact hexagonalBetaOfP_param hp1
  have hrbox : y.1 - x.1 ∈ box 2 r := by
    rw [mem_box_iff_siteRadius_le]
    change centeredRadius x.1 y.1 ≤ r
    exact le_rfl
  have hanchor := hexToTriAnchor_sub_mem_box_add_two hrbox
  have hdistNat :=
    hexagonal_dist_le_four_mul_add_two_of_anchor_sub_mem_box hanchor
  have hdist : (hexagonalGraph.dist x y : Real) ≤ 4 * (r : Real) + 10 := by
    exact_mod_cast hdistNat
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hrate : c * (hexagonalGraph.dist x y : Real) ≤
      ((r : Real) / Q) * delta + 10 * c := by
    calc
      c * (hexagonalGraph.dist x y : Real) ≤
          c * (4 * (r : Real) + 10) :=
        mul_le_mul_of_nonneg_left hdist hc.le
      _ = ((r : Real) / Q) * delta + 10 * c := by
        dsimp [c]
        field_simp
  by_cases hrzero : r = 0
  · have hone := hexagonal.wiredTwoPointProbability_le_one p q x y
    calc
      hexagonal.wiredTwoPointProbability p q x y ≤ 1 := hone
      _ ≤ C * Real.exp (-c * (hexagonalGraph.dist x y : Real)) := by
        rw [show (1 : Real) = Real.exp 0 by simp, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [C]
        have hrate0 : c * (hexagonalGraph.dist x y : Real) ≤ 10 * c := by
          simpa [hrzero] using hrate
        linarith
  · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hrzero
    have hpoint := hexagonal_wiredTwoPointProbability_le_theta
      r hr x y le_rfl q beta hq hbeta
    rw [hpEq] at hpoint
    have harm := hdecay r hr
    calc
      hexagonal.wiredTwoPointProbability p q x y ≤
          hexagonalOuterInnerTheta q beta r := hpoint
      _ ≤ Real.exp (-(((r : Real) / Q) * delta)) := by
        simpa [delta, mul_assoc] using harm
      _ ≤ C * Real.exp (-c * (hexagonalGraph.dist x y : Real)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        dsimp [C]
        linarith

end StatMech.FK.PeriodicPlanar
