/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedThreshold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedIntegration.Part2
import Theorem.StatisticalMechanics.Code.OSSS.BetaThresholdBound
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit.Part2
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedThreshold.Part4
open scoped BigOperators Classical
open Finset Set Filter Topology
open MeasureTheory


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedThreshold

open Lattice FK

open FKSharpnessWeightedPeriodic FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedStrict FKSharpnessWeightedIntegration

open FKSharpnessWeightedCoherentLimit

open IntegrationSubcritical BetaThresholdBound

open BetaCMatch LogCesaroLimit

theorem weightedHighBetaWitness_threshold_member
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta0) :
    exists betaStar : Real, 0 < betaStar /\ betaStar < beta0 /\
      betaStar ∈ thresholdSet (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  obtain ⟨betaStar, hbetaStar, hstar0, hTheta⟩ := hhigh
  exact ⟨betaStar, hbetaStar, hstar0,
    weightedThresholdSet_mem_of_selectedPhaseSum_pos
      d phaseJ hJ Jmin Jmax q beta0 betaStar
        hJmin hq hbetaStar hTheta⟩


theorem weightedHighBetaWitness_threshold_nonempty
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta0) :
    (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty := by
  obtain ⟨betaStar, _hbetaStar, _hstar0, hmem⟩ :=
    weightedHighBetaWitness_threshold_member
      d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh
  exact ⟨betaStar, hmem⟩


theorem weightedHighBetaWitness_strict_cutoff
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta0) :
    beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0 := by
  obtain ⟨betaStar, _hbetaStar, hstar0, hmem⟩ :=
    weightedHighBetaWitness_threshold_member
      d phaseJ hJ Jmin Jmax q beta0 hJmin hq hhigh
  have hle : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) <=
      betaStar := by
    unfold beta1
    exact csInf_le
      (weightedThresholdSet_bddBelow
        d phaseJ Jmin Jmax q beta0 hJmin) hmem
  exact hle.trans_lt hstar0

theorem weightedThresholdSig_of_pos
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 beta : Real) (hbeta : 0 < beta) :
    Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta =
      Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
  unfold Sig
  apply Finset.sum_congr rfl
  intro k hk
  exact weightedThresholdPhaseSum_of_pos
    d k phaseJ Jmin Jmax q beta0 beta hbeta


theorem weightedSelectedPhaseSum_difference_lower
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 beta' beta : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcrit : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta')
    (hbeta : beta' <= beta) (hupper : beta <= beta0) :
    beta - beta' <=
      weightedSelectedPhaseSum d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) beta /
        weightedPhaseSharpConstant d Jmin Jmax beta0 -
      weightedSelectedPhaseSum d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) beta' /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let f := weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0
  let fp := weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0
  let S := Sig f
  have hbeta1nn : 0 <= beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
    unfold beta1
    apply le_csInf hne
    intro x hx
    exact weightedThresholdSet_nonneg
      d phaseJ Jmin Jmax q beta0 hJmin x hx
  have hbeta'pos : 0 < beta' := lt_of_le_of_lt hbeta1nn hcrit
  have hbetapos : 0 < beta := hbeta'pos.trans_le hbeta
  have hf : forall i x, x ∈ Icc beta' beta ->
      HasDerivAt (fun x => f i x) (fp i x) x := by
    intro i x hx
    by_cases hi : i = 0
    · subst i
      have hconst : f 0 = fun _ => (Fintype.card P : Real) /
          weightedPhaseSharpConstant d Jmin Jmax beta0 := by
        funext z
        simp [f, weightedNormalizedPhaseSum]
      rw [hconst]
      simpa [fp, weightedNormalizedPhaseSumPrime, weightedPhaseSum] using
        (hasDerivAt_const x ((Fintype.card P : Real) /
          weightedPhaseSharpConstant d Jmin Jmax beta0))
    · exact weightedNormalizedPhaseSum_hasDerivAt
        d i (Nat.one_le_iff_ne_zero.mpr hi) phaseJ hp
          Jmin Jmax q beta0 x hq (hbeta'pos.trans_le hx.1)
  have hfnn : forall i x, 1 <= i -> x ∈ Icc beta' beta -> 0 <= f i x := by
    intro i x hi hx
    exact weightedNormalizedPhaseSum_nonneg d i phaseJ hp
      Jmin Jmax q beta0 x hJmin hq (hbeta'pos.trans_le hx.1)
  have hSpos : forall i x, 1 <= i -> x ∈ Icc beta' beta -> 0 < S i x := by
    intro i x hi hx
    rw [show S i x = Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) i x by
      symm
      simpa [S, f] using weightedThresholdSig_of_pos
        d i phaseJ Jmin Jmax q beta0 x (hbeta'pos.trans_le hx.1)]
    exact weightedThresholdSig_pos d i hi phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hdiff : forall i : Nat, forall x, 1 <= i -> x ∈ Icc beta' beta ->
      ((i : Real) / S i x) * f i x <= fp i x := by
    intro i x hi hx
    exact weightedNormalizedPhaseSum_differential
      d i hi J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q x beta0 hq (hbeta'pos.trans_le hx.1) (hx.2.trans hupper)
  have hSmono : forall n x, 1 <= n -> x ∈ Icc beta' beta ->
      S n beta' <= S (n + 1) x := by
    intro n x hn hx
    have hmono : S n beta' <= S n x := by
      unfold S Sig
      exact Finset.sum_le_sum fun k hk =>
        weightedNormalizedPhaseSum_mono_beta
          d k J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta' x hq hbeta'pos hx.1
    rw [show S (n + 1) x = S n x + f n x by
      exact IntegrationSubcritical.isc_Sig_succ f n x]
    exact hmono.trans (le_add_of_nonneg_right (hfnn n x hn hx))
  have hS1le : forall x, x ∈ Icc beta' beta ->
      S 1 x <= (Fintype.card P : Real) /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
    intro x hx
    simp [S, f, Sig, weightedNormalizedPhaseSum]
  have hTbeta := weightedNormalizedPhaseSum_meanLogTerm_tendsto
    d phaseJ hp Jmin Jmax q beta0 beta hq hbetapos
  have hTbeta' := weightedNormalizedPhaseSum_meanLogTerm_tendsto
    d phaseJ hp Jmin Jmax q beta0 beta' hq hbeta'pos
  have hSigEq : (fun n => S n beta') = (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta') := by
    funext n
    symm
    simpa [S, f] using weightedThresholdSig_of_pos
      d n phaseJ Jmin Jmax q beta0 beta' hbeta'pos
  have hcob : IsCoboundedUnder (· <= ·) atTop
      (logRatio (fun n => S n beta')) := by
    rw [hSigEq]
    exact weightedThresholdLogRatio_isCobounded
      d phaseJ hp Jmin Jmax q beta0 beta' hJmin hq
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (logRatio (fun n => S n beta')) := by
    rw [hSigEq]
    exact weightedThresholdLogRatio_bddAbove
      d phaseJ hp Jmin Jmax q beta0 beta' hJmin hq
  have hm1 : 1 <= limsup (logRatio (fun n => S n beta')) atTop := by
    rw [hSigEq]
    exact one_le_limsup_of_beta1_lt hne
      (fun hab n => weightedThresholdSig_mono_beta
        d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 hq hab)
      (fun x n hn => weightedThresholdSig_pos d n (by omega) phaseJ hp
        Jmin Jmax q beta0 x hJmin hq)
      (fun x => weightedThresholdLogRatio_isCobounded
        d phaseJ hp Jmin Jmax q beta0 x hJmin hq)
      (fun x => weightedThresholdLogRatio_bddAbove
        d phaseJ hp Jmin Jmax q beta0 x hJmin hq)
      hcrit
  exact meanField_lower_of_threshold_rate f fp S beta' beta
    (weightedSelectedPhaseSum d phaseJ hp q
      (zero_lt_one.trans_le hq) beta /
        weightedPhaseSharpConstant d Jmin Jmax beta0)
    (weightedSelectedPhaseSum d phaseJ hp q
      (zero_lt_one.trans_le hq) beta' /
        weightedPhaseSharpConstant d Jmin Jmax beta0)
    ((Fintype.card P : Real) /
      weightedPhaseSharpConstant d Jmin Jmax beta0)
    hbeta hf (IntegrationSubcritical.isc_Sig_succ f) hfnn hSpos hdiff
      hSmono hS1le hTbeta hTbeta' hcob hbdd hm1


theorem weightedSelectedPhaseSum_meanField_lower
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 beta : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcrit : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta)
    (hupper : beta <= beta0) :
    weightedPhaseSharpConstant d Jmin Jmax beta0 *
        (beta - beta1 (fun b n => Sig
          (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) <=
      weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) beta := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  let c := weightedPhaseSharpConstant d Jmin Jmax beta0
  have hc : 0 < c := weightedPhaseSharpConstant_pos d hJmin
  have hnormalized : beta - betaOne <=
      weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) beta / c := by
    apply meanField_lower_at_threshold
      (f := fun x => weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) x / c)
      (β₁ := betaOne) (β := beta) hcrit
    · intro x hx1 hxb
      exact div_nonneg (weightedSelectedPhaseSum_nonneg
        d phaseJ hp q (zero_lt_one.trans_le hq) x) hc.le
    · intro x hx1 hxb
      exact weightedSelectedPhaseSum_difference_lower
        d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 x beta hq hne hx1 hxb.le hupper
  simpa [betaOne, c, hp, mul_comm] using (le_div_iff₀ hc).mp hnormalized


theorem weightedSelectedPhaseSum_mono_pos
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 a b : Real) (hq : 1 <= q) (ha : 0 < a) (hab : a <= b) :
    weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) a <=
      weightedSelectedPhaseSum d phaseJ
        (hcov.phaseCoupling_pos hsurj
          (fun e => hJmin.trans_le (hJlo e))) q
        (zero_lt_one.trans_le hq) b := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hc : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 :=
    weightedPhaseSharpConstant_pos d hJmin
  have hTa := weightedNormalizedPhaseSum_tendsto
    d phaseJ hp Jmin Jmax q beta0 a hq ha
  have hTb := weightedNormalizedPhaseSum_tendsto
    d phaseJ hp Jmin Jmax q beta0 b hq (ha.trans_le hab)
  have hle : weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) a /
        weightedPhaseSharpConstant d Jmin Jmax beta0 <=
      weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) b /
        weightedPhaseSharpConstant d Jmin Jmax beta0 :=
    le_of_tendsto_of_tendsto hTa hTb <| Eventually.of_forall fun n =>
      weightedNormalizedPhaseSum_mono_beta
        d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q beta0 a b hq ha hab
  exact (div_le_div_iff_of_pos_right hc).mp hle


theorem weightedPhaseSum_subcritical_decay_of_threshold
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0) (hdelta : 0 < delta)
    (hleft : 0 < beta - 2 * delta)
    (hlt : beta < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    exists Q : Real, 0 < Q ∧ forall n : Nat, 1 <= n ->
      weightedPhaseSum d phaseJ q (beta - 2 * delta) n <=
        (Fintype.card P : Real) *
          Real.exp (-(((n : Real) / Q) * delta)) := by
  let f := weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0
  let f' := weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0
  let c := weightedPhaseSharpConstant d Jmin Jmax beta0
  let M := (Fintype.card P : Real) / c
  have hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hc : 0 < c := weightedPhaseSharpConstant_pos d hJmin
  have hM : 0 <= M := div_nonneg (Nat.cast_nonneg _) hc.le
  have hinterval : ∀ x, x ∈ Icc (beta - 2 * delta) beta -> 0 < x := by
    intro x hx
    exact hleft.trans_le hx.1
  have hd : forall n x, x ∈ Icc (beta - 2 * delta) beta ->
      HasDerivAt (f n) (f' n x) x := by
    intro n x hx
    by_cases hn0 : n = 0
    · subst n
      have hconst : f 0 = fun _ => M := by
        funext z
        simp [f, M, c, weightedThresholdPhaseSum,
          weightedNormalizedPhaseSum]
      rw [hconst]
      simpa [f', weightedNormalizedPhaseSumPrime,
        weightedPhaseSum] using (hasDerivAt_const x M)
    · have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
      have hnorm := weightedNormalizedPhaseSum_hasDerivAt
        d n hn phaseJ hp Jmin Jmax q beta0 x hq (hinterval x hx)
      refine hnorm.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds (hinterval x hx)] with z hz
      have hz0 : 0 < z := hz
      simp [f, weightedThresholdPhaseSum, not_le.mpr hz0]
  have hfnn : forall n x, x ∈ Icc (beta - 2 * delta) beta ->
      0 <= f n x := by
    intro n x hx
    exact weightedThresholdPhaseSum_nonneg d n phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hfM : forall n x, x ∈ Icc (beta - 2 * delta) beta ->
      f n x <= M := by
    intro n x hx
    exact weightedThresholdPhaseSum_le_card_div d n phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hfmono : forall k : Nat, forall {y x},
      y ∈ Icc (beta - 2 * delta) beta ->
      x ∈ Icc (beta - 2 * delta) beta -> y <= x -> f k y <= f k x := by
    intro k y x hy hx hyx
    exact weightedThresholdPhaseSum_mono_beta
      d k J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 y x hq hyx
  have hSpos : forall n, 1 <= n -> forall x,
      x ∈ Icc (beta - 2 * delta) beta -> 0 < Sig f n x := by
    intro n hn x hx
    exact weightedThresholdSig_pos d n hn phaseJ hp
      Jmin Jmax q beta0 x hJmin hq
  have hdiff : forall n : Nat, 1 <= n -> forall x,
      x ∈ Icc (beta - 2 * delta) beta ->
        ((n : Real) / Sig f n x) * f n x <= f' n x := by
    intro n hn x hx
    rw [show Sig f n x = Sig
        (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n x by
      simpa [f] using weightedThresholdSig_of_pos
        d n phaseJ Jmin Jmax q beta0 x (hinterval x hx)]
    rw [show f n x = weightedNormalizedPhaseSum
        d phaseJ Jmin Jmax q beta0 n x by
      simp [f, weightedThresholdPhaseSum, not_le.mpr (hinterval x hx)]]
    exact weightedNormalizedPhaseSum_differential
      d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q x beta0 hq (hinterval x hx) (hx.2.trans hbeta0)
  have hSbeta : forall n, 2 <= n -> 0 < Sig f n beta := by
    intro n hn
    exact weightedThresholdSig_pos d n (by omega) phaseJ hp
      Jmin Jmax q beta0 beta hJmin hq
  have hbddSet : BddBelow (thresholdSet (fun b n => Sig f n b)) := by
    simpa [f] using weightedThresholdSet_bddBelow
      d phaseJ Jmin Jmax q beta0 hJmin
  have hbdd : IsBoundedUnder (· <= ·) atTop
      (logRatio (fun n => Sig f n beta)) := by
    simpa [f] using weightedThresholdLogRatio_bddAbove
      d phaseJ hp Jmin Jmax q beta0 beta hJmin hq
  obtain ⟨Q, hQ, hdecay⟩ := btb_subcritical_decay_of_threshold
    f f' delta beta M hdelta hM hd hfnn hfM hfmono hSpos hdiff
      hSbeta hbddSet hbdd (by simpa [f] using hlt)
  refine ⟨Q, hQ, ?_⟩
  intro n hn
  have h := hdecay n hn
  have hpos : 0 < beta - 2 * delta := hleft
  rw [show f n (beta - 2 * delta) =
      weightedPhaseSum d phaseJ q (beta - 2 * delta) n / c by
    simp [f, weightedThresholdPhaseSum, not_le.mpr hpos,
      weightedNormalizedPhaseSum, c]] at h
  have hrhs : M * Real.exp (-(((n : Real) / Q) * delta)) =
      ((Fintype.card P : Real) *
        Real.exp (-(((n : Real) / Q) * delta))) / c := by
    unfold M
    field_simp
  rw [hrhs] at h
  exact (div_le_div_iff_of_pos_right hc).mp h


theorem weightedPhasePhysical_subcritical_decay_of_threshold
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q delta beta beta0 : Real) (hq : 1 <= q)
    (hbeta0 : beta <= beta0) (hdelta : 0 < delta)
    (hleft : 0 < beta - 2 * delta)
    (hlt : beta < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    exists Q : Real, 0 < Q ∧ forall a : P, forall n : Nat, 2 <= n ->
      ((weightedPhaseFiniteMeasure d n phaseJ a
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e)) a)
          q (beta - 2 * delta) (zero_lt_one.trans_le hq) hleft :
          ProbabilityMeasure _) : Measure _).real (boxBdryConnEvent d n) <=
        (Fintype.card P : Real) *
          Real.exp (-((((n : Real) / (3 * Q)) * delta))) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  obtain ⟨Q, hQ, hdecay⟩ := weightedPhaseSum_subcritical_decay_of_threshold
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q delta beta beta0 hq hbeta0 hdelta hleft hlt
  refine ⟨Q, hQ, ?_⟩
  intro a n hn
  let k := n / 2
  have hk : 1 <= k := by dsimp [k]; omega
  have hnk : n <= 3 * k := by dsimp [k]; omega
  have hphysical := weightedPhasePhysical_le_localized_half
    d n hn phaseJ hp a q (beta - 2 * delta) hq hleft
  have hprofileSum : weightedPhaseProfile d phaseJ a q
      (beta - 2 * delta) k <=
      weightedPhaseSum d phaseJ q (beta - 2 * delta) k := by
    unfold weightedPhaseSum
    exact Finset.single_le_sum
      (fun b hb => weightedPhaseProfile_nonneg d phaseJ hp b q
        (beta - 2 * delta) hq hleft k) (Finset.mem_univ a)
  have hloc := hdecay k hk
  have hrate : (n : Real) / (3 * Q) <= (k : Real) / Q := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hQ) hQ]
    have hnkR : (n : Real) <= 3 * (k : Real) := by exact_mod_cast hnk
    nlinarith
  calc
    _ <= weightedPhaseProfile d phaseJ a q (beta - 2 * delta) k := by
      simpa [k] using hphysical
    _ <= weightedPhaseSum d phaseJ q (beta - 2 * delta) k := hprofileSum
    _ <= (Fintype.card P : Real) *
        Real.exp (-(((k : Real) / Q) * delta)) := hloc
    _ <= (Fintype.card P : Real) *
        Real.exp (-(((n : Real) / (3 * Q)) * delta)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith


theorem weightedSelectedPhaseSum_eq_zero_below_threshold
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 beta : Real) (hq : 1 <= q)
    (hcut : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0)
    (hbelow : beta < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    weightedSelectedPhaseSum d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta = 0 := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  by_cases hbeta : 0 < beta
  · let betaMid := (beta + beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) / 2
    let delta := (betaMid - beta) / 2
    have hmidLower : beta < betaMid := by dsimp [betaMid]; linarith
    have hmidUpper : betaMid < beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
      dsimp [betaMid]
      linarith
    have hdelta : 0 < delta := by dsimp [delta]; linarith
    have hleft : betaMid - 2 * delta = beta := by
      dsimp [delta, betaMid]
      ring
    have hmidCut : betaMid <= beta0 := (hmidUpper.trans hcut).le
    obtain ⟨Q, hQ, hdecay⟩ := weightedPhaseSum_subcritical_decay_of_threshold
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q delta betaMid beta0 hq hmidCut hdelta (hleft.symm ▸ hbeta) hmidUpper
    have hconv := weightedPhaseSum_tendsto_selectedPhaseSum
      d phaseJ hp q beta hq hbeta
    have hzero := bcm_expBound_tendsto_zero (Fintype.card P : Real) Q delta hQ hdelta
    have hle : weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) beta <= 0 :=
      le_of_tendsto_of_tendsto hconv hzero <| by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simpa [hleft] using hdecay n hn
    exact le_antisymm hle (weightedSelectedPhaseSum_nonneg
      d phaseJ hp q (zero_lt_one.trans_le hq) beta)
  · unfold weightedSelectedPhaseSum weightedPhaseThetaProfile
    simp [hbeta]


theorem weightedThreshold_eq_selectedPhaseCritical
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcut : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0)
    (a : P) :
    sSup (bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) a)) =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  have hbeta1nn : 0 <= betaOne := by
    dsimp [betaOne]
    unfold beta1
    apply le_csInf hne
    intro x hx
    exact weightedThresholdSet_nonneg
      d phaseJ Jmin Jmax q beta0 hJmin x hx
  have hbeta0pos : 0 < beta0 := hbeta1nn.trans_lt hcut
  have htransport :=
    FKSharpnessWeightedPhaseClose.covariantWeightedPhasePositivityTransport
      J phase phaseJ (fun e => hJmin.trans_le (hJlo e))
        hsurj hcov q hq
  apply bcm_betaC_eq_threshold _ betaOne
  · intro beta hbeta
    have hsumzero := weightedSelectedPhaseSum_eq_zero_below_threshold
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 beta hq hcut hbeta
    have hnonneg := weightedPhaseThetaProfile_nonneg
      d phaseJ hp q (zero_lt_one.trans_le hq) a beta
    have hle : weightedPhaseThetaProfile d phaseJ hp q
        (zero_lt_one.trans_le hq) a beta <=
        weightedSelectedPhaseSum d phaseJ hp q
          (zero_lt_one.trans_le hq) beta := by
      unfold weightedSelectedPhaseSum
      exact Finset.single_le_sum
        (fun b hb => weightedPhaseThetaProfile_nonneg
          d phaseJ hp q (zero_lt_one.trans_le hq) b beta)
        (Finset.mem_univ a)
    linarith
  · intro beta hbeta
    have hsumpos : 0 < weightedSelectedPhaseSum d phaseJ hp q
        (zero_lt_one.trans_le hq) beta := by
      by_cases hupper : beta <= beta0
      · have hmf := weightedSelectedPhaseSum_meanField_lower
          d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta hq hne hbeta hupper
        have hgap : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 *
            (beta - betaOne) := mul_pos
          (weightedPhaseSharpConstant_pos d hJmin) (sub_pos.mpr hbeta)
        exact hgap.trans_le hmf
      · have hmf0 := weightedSelectedPhaseSum_meanField_lower
          d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta0 hq hne hcut le_rfl
        have hsum0 : 0 < weightedSelectedPhaseSum d phaseJ hp q
            (zero_lt_one.trans_le hq) beta0 := by
          have hgap0 : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 *
              (beta0 - betaOne) := mul_pos
            (weightedPhaseSharpConstant_pos d hJmin) (sub_pos.mpr hcut)
          exact hgap0.trans_le hmf0
        exact hsum0.trans_le (weightedSelectedPhaseSum_mono_pos
          d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
            q beta0 beta0 beta hq hbeta0pos (le_of_lt (lt_of_not_ge hupper)))
    change 0 < ∑ b : P, weightedPhaseThetaProfile d phaseJ hp q
      (zero_lt_one.trans_le hq) b beta at hsumpos
    obtain ⟨b, hb, hbpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun b hb => weightedPhaseThetaProfile_nonneg
        d phaseJ hp q (zero_lt_one.trans_le hq) b beta)).mp hsumpos
    exact (htransport b a beta).mp hbpos


theorem weightedThreshold_eq_selectedPhaseEnvelopeCritical
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hne : (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty)
    (hcut : beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) < beta0) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) a beta) = 0} =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let a : P := Classical.choice (inferInstance : Nonempty P)
  exact (FKSharpnessWeightedPhaseClose.covariant_weighted_phase_common_critical
    J phase phaseJ (fun e => hJmin.trans_le (hJlo e))
      hsurj hcov q hq a).trans
    (weightedThreshold_eq_selectedPhaseCritical
      d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 hq hne hcut a)


theorem weightedThreshold_eq_selectedPhaseCritical_of_highBetaWitness
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta0)
    (a : P) :
    sSup (bcm_subcriticalSet (weightedPhaseThetaProfile d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) a)) =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  have hcut := weightedHighBetaWitness_strict_cutoff
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  exact weightedThreshold_eq_selectedPhaseCritical
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 hq hne hcut a


theorem weightedThreshold_eq_selectedPhaseEnvelopeCritical_of_highBetaWitness
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q)
    (hhigh : weightedSelectedPhaseHighBetaWitness d phaseJ
      (hcov.phaseCoupling_pos hsurj
        (fun e => hJmin.trans_le (hJlo e))) q
      (zero_lt_one.trans_le hq) beta0) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun a => weightedPhaseThetaProfile d phaseJ
          (hcov.phaseCoupling_pos hsurj
            (fun e => hJmin.trans_le (hJlo e))) q
          (zero_lt_one.trans_le hq) a beta) = 0} =
      beta1 (fun b n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  have hcut := weightedHighBetaWitness_strict_cutoff
    d phaseJ hp Jmin Jmax q beta0 hJmin hq (by simpa [hp] using hhigh)
  exact weightedThreshold_eq_selectedPhaseEnvelopeCritical
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 hq hne hcut

end FKSharpnessWeightedThreshold
end OSSS
end StatMech
