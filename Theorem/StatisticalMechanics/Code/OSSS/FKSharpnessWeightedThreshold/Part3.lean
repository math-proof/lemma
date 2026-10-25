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
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedThreshold.Part3
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

theorem weightedThresholdPhaseSum_of_pos
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 beta : Real) (hbeta : 0 < beta) :
    weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta =
      weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
  simp [weightedThresholdPhaseSum, not_le.mpr hbeta]

theorem weightedNormalizedPhaseSumSig_eq
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 beta : Real) :
    Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta =
      weightedPhaseSumSig d n phaseJ q beta /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  unfold Sig weightedNormalizedPhaseSum weightedPhaseSumSig
  rw [Finset.sum_div]

theorem weightedPhaseSum_differentiableAt
    (d n : Nat) (hn : 1 <= n) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    DifferentiableAt Real (fun b => weightedPhaseSum d phaseJ q b n) beta := by
  unfold weightedPhaseSum
  exact DifferentiableAt.fun_sum fun a ha =>
    weightedPhaseProfile_differentiableAt d n hn phaseJ hJ a q beta hq hbeta

theorem weightedNormalizedPhaseSum_hasDerivAt
    (d n : Nat) (hn : 1 <= n) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    HasDerivAt
      (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n)
      (weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta)
      beta := by
  have hd := weightedPhaseSum_differentiableAt
    d n hn phaseJ hJ q beta hq hbeta
  simpa [weightedNormalizedPhaseSum, weightedNormalizedPhaseSumPrime,
    div_eq_mul_inv, mul_comm] using hd.hasDerivAt.const_mul
      (weightedPhaseSharpConstant d Jmin Jmax beta0)⁻¹

theorem weightedNormalizedPhaseSum_differential
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta beta0 : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    (((n : Real) /
        Sig (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta) *
      weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta) <=
        weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n beta := by
  have hc := weightedPhaseSharpConstant_pos d
    (Jmax := Jmax) (beta0 := beta0) hJmin
  have hmain := weightedPhaseSum_differential_integration
    d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta beta0 hq hbeta hbeta0
  rw [weightedNormalizedPhaseSumSig_eq]
  unfold weightedNormalizedPhaseSum weightedNormalizedPhaseSumPrime
  rw [le_div_iff₀ hc]
  convert hmain using 1
  unfold weightedPhaseSharpConstant
  rw [Nat.mul_comm 2 d]
  field_simp

theorem weightedPhaseProfile_le_one
    (d n : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseProfile d phaseJ a q beta n <= 1 := by
  by_cases hn0 : n = 0
  · simp [weightedPhaseProfile, hn0]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  rw [weightedPhaseProfile, if_neg hn0,
    weightedPhaseWiredTheta_eq_finiteMeasure_double
      d n hn phaseJ a (hJ a) q beta hq hbeta]
  exact measureReal_le_one

@[simp] theorem weightedPhaseSum_zero
    (d : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) :
    weightedPhaseSum d phaseJ q beta 0 = Fintype.card P := by
  simp [weightedPhaseSum]

theorem weightedPhaseSum_nonneg
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= weightedPhaseSum d phaseJ q beta n := by
  unfold weightedPhaseSum
  exact Finset.sum_nonneg fun a ha =>
    weightedPhaseProfile_nonneg d phaseJ hJ a q beta hq hbeta n

theorem weightedPhaseSum_le_card
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseSum d phaseJ q beta n <= Fintype.card P := by
  unfold weightedPhaseSum
  calc
    (∑ a : P, weightedPhaseProfile d phaseJ a q beta n) <=
        ∑ _a : P, (1 : Real) := Finset.sum_le_sum fun a ha =>
          weightedPhaseProfile_le_one d n phaseJ hJ a q beta hq hbeta
    _ = Fintype.card P := by simp

theorem weightedPhaseSumSig_pos
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 < weightedPhaseSumSig d n phaseJ q beta := by
  have hzero : 0 < weightedPhaseSum d phaseJ q beta 0 := by
    rw [weightedPhaseSum_zero]
    exact_mod_cast Fintype.card_pos
  unfold weightedPhaseSumSig
  exact hzero.trans_le (Finset.single_le_sum
    (fun k hk => weightedPhaseSum_nonneg d k phaseJ hJ q beta hq hbeta)
    (Finset.mem_range.mpr hn))

theorem weightedNormalizedPhaseSum_nonneg
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
  exact div_nonneg (weightedPhaseSum_nonneg d n phaseJ hJ q beta hq hbeta)
    (weightedPhaseSharpConstant_pos d hJmin).le

theorem weightedNormalizedPhaseSum_le_card_div
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n beta <=
      (Fintype.card P : Real) / weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  unfold weightedNormalizedPhaseSum
  exact div_le_div_of_nonneg_right
    (weightedPhaseSum_le_card d n phaseJ hJ q beta hq hbeta)
    (weightedPhaseSharpConstant_pos d hJmin).le

theorem weightedNormalizedPhaseSumPrime_nonneg
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta beta0 : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) :
    0 <= weightedNormalizedPhaseSumPrime
      d phaseJ Jmin Jmax q beta0 n beta := by
  have hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hSig := weightedPhaseSumSig_pos d n hn phaseJ hp q beta hq hbeta
  have hfnn := weightedPhaseSum_nonneg d n phaseJ hp q beta hq hbeta
  have hcBeta : 0 < weightedPhaseSharpConstant d Jmin Jmax beta :=
    weightedPhaseSharpConstant_pos d hJmin
  have hlhs : 0 <= weightedPhaseSharpConstant d Jmin Jmax beta *
      (((n : Real) / weightedPhaseSumSig d n phaseJ q beta) *
        weightedPhaseSum d phaseJ q beta n) :=
    mul_nonneg hcBeta.le
      (mul_nonneg (div_nonneg (Nat.cast_nonneg n) hSig.le) hfnn)
  have hraw := weightedPhaseSum_differential_integration
    d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta beta hq hbeta le_rfl
  unfold weightedNormalizedPhaseSumPrime
  exact div_nonneg (hlhs.trans hraw)
    (weightedPhaseSharpConstant_pos d hJmin).le

theorem weightedNormalizedPhaseSum_mono_beta
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 y x : Real) (hq : 1 <= q)
    (hy : 0 < y) (hyx : y <= x) :
    weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n y <=
      weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n x := by
  by_cases hn0 : n = 0
  · subst n
    simp [weightedNormalizedPhaseSum]
  have hn : 1 <= n := Nat.one_le_iff_ne_zero.mpr hn0
  let f := weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0 n
  let f' := weightedNormalizedPhaseSumPrime d phaseJ Jmin Jmax q beta0 n
  have hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  have hd : forall z, z ∈ Icc y x -> HasDerivAt f (f' z) z := by
    intro z hz
    exact weightedNormalizedPhaseSum_hasDerivAt
      d n hn phaseJ hp Jmin Jmax q beta0 z hq (hy.trans_le hz.1)
  have hmono : MonotoneOn f (Icc y x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y x)
    · intro z hz
      exact (hd z hz).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      exact (hd z (mem_Icc_of_Ioo hz)).differentiableAt.differentiableWithinAt
    · intro z hz
      rw [interior_Icc] at hz
      rw [(hd z (mem_Icc_of_Ioo hz)).deriv]
      exact weightedNormalizedPhaseSumPrime_nonneg
        d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
          q z beta0 hq (hy.trans hz.1)
  exact hmono (left_mem_Icc.mpr hyx) (right_mem_Icc.mpr hyx) hyx

theorem weightedThresholdPhaseSum_nonneg
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    0 <= weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · rw [weightedThresholdPhaseSum, if_pos hbeta, if_pos hn0]
      exact div_nonneg (Nat.cast_nonneg _)
        (weightedPhaseSharpConstant_pos d hJmin).le
    · simp [weightedThresholdPhaseSum, hbeta, hn0]
  · rw [weightedThresholdPhaseSum_of_pos d n phaseJ
      Jmin Jmax q beta0 beta (lt_of_not_ge hbeta)]
    exact weightedNormalizedPhaseSum_nonneg d n phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq (lt_of_not_ge hbeta)

theorem weightedThresholdPhaseSum_le_card_div
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n beta <=
      (Fintype.card P : Real) /
        weightedPhaseSharpConstant d Jmin Jmax beta0 := by
  by_cases hbeta : beta <= 0
  · by_cases hn0 : n = 0
    · simp [weightedThresholdPhaseSum, hbeta, hn0]
    · rw [weightedThresholdPhaseSum, if_pos hbeta, if_neg hn0]
      exact div_nonneg (Nat.cast_nonneg _) (weightedPhaseSharpConstant_pos
        d hJmin).le
  · rw [weightedThresholdPhaseSum_of_pos d n phaseJ
      Jmin Jmax q beta0 beta (lt_of_not_ge hbeta)]
    exact weightedNormalizedPhaseSum_le_card_div d n phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq (lt_of_not_ge hbeta)

theorem weightedThresholdPhaseSum_mono_beta
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 a b : Real) (hq : 1 <= q) (hab : a <= b) :
    weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n a <=
      weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 n b := by
  let hp := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  by_cases hb : b <= 0
  · have ha : a <= 0 := hab.trans hb
    simp [weightedThresholdPhaseSum, ha, hb]
  by_cases ha : a <= 0
  · by_cases hn0 : n = 0
    · subst n
      simp [weightedThresholdPhaseSum, ha, hb, weightedNormalizedPhaseSum]
    · rw [weightedThresholdPhaseSum, if_pos ha, if_neg hn0,
        weightedThresholdPhaseSum, if_neg hb]
      exact weightedNormalizedPhaseSum_nonneg d n phaseJ hp
        Jmin Jmax q beta0 b hJmin hq (lt_of_not_ge hb)
  · rw [weightedThresholdPhaseSum_of_pos d n phaseJ
        Jmin Jmax q beta0 a (lt_of_not_ge ha),
      weightedThresholdPhaseSum_of_pos d n phaseJ
        Jmin Jmax q beta0 b (lt_of_not_ge hb)]
    exact weightedNormalizedPhaseSum_mono_beta
      d n J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta0 a b hq (lt_of_not_ge ha) hab

theorem weightedThresholdSig_mono_beta
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta0 : Real) (hq : 1 <= q) {a b : Real} (hab : a <= b) :
    Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n a <=
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b := by
  unfold Sig
  exact Finset.sum_le_sum fun k hk => weightedThresholdPhaseSum_mono_beta
    d k J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 a b hq hab

theorem weightedThresholdSig_pos
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    0 < Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
  have hzero : 0 < weightedThresholdPhaseSum
      d phaseJ Jmin Jmax q beta0 0 beta := by
    by_cases hbeta : beta <= 0
    · rw [weightedThresholdPhaseSum, if_pos hbeta, if_pos rfl]
      exact div_pos (by exact_mod_cast Fintype.card_pos)
        (weightedPhaseSharpConstant_pos d hJmin)
    · rw [weightedThresholdPhaseSum_of_pos d 0 phaseJ
        Jmin Jmax q beta0 beta (lt_of_not_ge hbeta)]
      unfold weightedNormalizedPhaseSum
      rw [weightedPhaseSum_zero]
      exact div_pos (by exact_mod_cast Fintype.card_pos)
        (weightedPhaseSharpConstant_pos d hJmin)
  unfold Sig
  exact hzero.trans_le (Finset.single_le_sum
    (fun k hk => weightedThresholdPhaseSum_nonneg d k phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq) (Finset.mem_range.mpr hn))

theorem weightedThresholdSig_le_linear
    (d n : Nat) {P : Type*} [Fintype P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta <=
      ((Fintype.card P : Real) /
        weightedPhaseSharpConstant d Jmin Jmax beta0) * (n : Real) := by
  unfold Sig
  calc
    (∑ k ∈ Finset.range n,
      weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0 k beta) <=
        ∑ _k ∈ Finset.range n, ((Fintype.card P : Real) /
          weightedPhaseSharpConstant d Jmin Jmax beta0) :=
      Finset.sum_le_sum fun k hk => weightedThresholdPhaseSum_le_card_div
        d k phaseJ hJ Jmin Jmax q beta0 beta hJmin hq
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

theorem weightedThresholdSet_nonneg
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin)
    (beta : Real)
    (hmem : beta ∈ thresholdSet (fun b n =>
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) :
    0 <= beta := by
  by_contra hbeta
  have hbetaNeg : beta < 0 := lt_of_not_ge hbeta
  let c := (Fintype.card P : Real) /
    weightedPhaseSharpConstant d Jmin Jmax beta0
  have hc : 0 < c := div_pos (by exact_mod_cast Fintype.card_pos)
    (weightedPhaseSharpConstant_pos d hJmin)
  have hsig : forall n, 1 <= n ->
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta = c := by
    intro n hn
    unfold Sig weightedThresholdPhaseSum
    simp only [if_pos (le_of_lt hbetaNeg)]
    rw [Finset.sum_eq_single 0]
    · simp [c]
    · intro k hk hk0
      simp [hk0]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr hn)).elim
  have htend : Tendsto
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
      atTop (nhds 0) := by
    have hlog : Tendsto (fun n : Nat => Real.log (n : Real)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : Nat => Real.log c / Real.log (n : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
    apply hdiv.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [logRatio, hsig n hn]
  have hlimsup : Filter.limsup
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
      atTop = 0 := htend.limsup_eq
  change (1 : Real) <= Filter.limsup
    (logRatio (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
      atTop at hmem
  rw [hlimsup] at hmem
  norm_num at hmem

theorem weightedThresholdSet_bddBelow
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (Jmin Jmax q beta0 : Real) (hJmin : 0 < Jmin) :
    BddBelow (thresholdSet (fun b n =>
      Sig (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)) := by
  exact ⟨0, fun beta hmem => weightedThresholdSet_nonneg
    d phaseJ Jmin Jmax q beta0 hJmin beta hmem⟩

theorem weightedThresholdLogRatio_bddAbove
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    Filter.IsBoundedUnder (fun x y : Real => x <= y) atTop
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) := by
  let M := (Fintype.card P : Real) /
    weightedPhaseSharpConstant d Jmin Jmax beta0
  let C := max 1 M
  have hC : 1 <= C := le_max_left _ _
  have hMC : M <= C := le_max_right _ _
  apply btb_bddAbove_ratio_of_linear
    (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)
    C hC
  · intro n hn
    exact weightedThresholdSig_pos d n (by omega) phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq
  · intro n
    exact (weightedThresholdSig_le_linear d n phaseJ hJ
      Jmin Jmax q beta0 beta hJmin hq).trans
        (mul_le_mul_of_nonneg_right hMC (Nat.cast_nonneg n))

theorem weightedThresholdLogRatio_isCobounded
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) :
    Filter.IsCoboundedUnder (fun x y : Real => x <= y) atTop
      (logRatio (fun n => Sig
        (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) := by
  let c := (Fintype.card P : Real) /
    weightedPhaseSharpConstant d Jmin Jmax beta0
  have hc : 0 < c := div_pos (by exact_mod_cast Fintype.card_pos)
    (weightedPhaseSharpConstant_pos d hJmin)
  have hdiv : Tendsto (fun n : Nat => Real.log c / Real.log (n : Real))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine Filter.isCoboundedUnder_le_of_eventually_le
    (f := logRatio (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta))
    (x := -1) atTop ?_
  have hev : ∀ᶠ n : Nat in atTop,
      -1 <= Real.log c / Real.log (n : Real) :=
    hdiv.eventually (Ici_mem_nhds (by norm_num : (-1 : Real) < 0))
  filter_upwards [eventually_ge_atTop 2, hev] with n hn hcn
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hsig : c <= Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta := by
    have hzero : weightedThresholdPhaseSum
        d phaseJ Jmin Jmax q beta0 0 beta = c := by
      by_cases hbeta : beta <= 0
      · simp [weightedThresholdPhaseSum, hbeta, c]
      · simp [weightedThresholdPhaseSum, hbeta, weightedNormalizedPhaseSum,
          weightedPhaseSum_zero, c]
    rw [← hzero]
    unfold Sig
    exact Finset.single_le_sum
      (fun k hk => weightedThresholdPhaseSum_nonneg d k phaseJ hJ
        Jmin Jmax q beta0 beta hJmin hq) (Finset.mem_range.mpr (by omega))
  exact hcn.trans ((div_le_div_iff_of_pos_right hlogn).2
    (Real.log_le_log hc hsig))


theorem weightedThresholdSet_mem_of_selectedPhaseSum_pos
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (hTheta : 0 < weightedSelectedPhaseSum d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta) :
    beta ∈ thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  have hc := weightedPhaseSharpConstant_pos d
    (Jmax := Jmax) (beta0 := beta0) hJmin
  have hconv := weightedNormalizedPhaseSum_tendsto
    d phaseJ hJ Jmin Jmax q beta0 beta hq hbeta
  have hratio := logRatio_partialSum_tendsto_one hconv (div_pos hTheta hc)
  change 1 <= Filter.limsup (logRatio (fun n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta)) atTop
  have hsig : (fun n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n beta) =
      (fun n => Sig
        (weightedNormalizedPhaseSum d phaseJ Jmin Jmax q beta0) n beta) := by
    funext n
    unfold Sig
    apply Finset.sum_congr rfl
    intro k hk
    exact weightedThresholdPhaseSum_of_pos
      d k phaseJ Jmin Jmax q beta0 beta hbeta
  rw [hsig]
  unfold Sig
  rw [hratio.limsup_eq]

theorem weightedThresholdSet_nonempty_of_selectedPhaseSum_pos
    (d : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (Jmin Jmax q beta0 beta : Real) (hJmin : 0 < Jmin)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (hTheta : 0 < weightedSelectedPhaseSum d phaseJ hJ q
      (zero_lt_one.trans_le hq) beta) :
    (thresholdSet (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)).Nonempty :=
  ⟨beta, weightedThresholdSet_mem_of_selectedPhaseSum_pos
    d phaseJ hJ Jmin Jmax q beta0 beta hJmin hq hbeta hTheta⟩


end FKSharpnessWeightedThreshold
end OSSS
end StatMech
