/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedPhasewiseMeanField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedHighBeta
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedPhasewiseMeanField
open scoped BigOperators
open Finset Set Filter Topology MeasureTheory


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedPhasewiseMeanField

open Lattice FK Percolation

open BetaThresholdBound IntegrationSubcritical

open FKSharpnessWeightedPeriodic

open FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedThreshold

open FKSharpnessWeightedCoherentLimit

open FKSharpnessWeightedSelectedLaws

open FKSharpnessWeightedPhaseTransport

open FKSharpnessWeightedPhaseClose


theorem weightedPhaseFinite_shell_le_wiredFinite
    (d k R : Nat) (hkR : k <= R) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmax : Real) (hJhi : forall e, phaseJ a e <= Jmax)
    (q beta p : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hp : 0 < p) (hp1 : p < 1)
    (hpmax : 1 - Real.exp (-(beta * Jmax)) <= p) :
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) <=
      (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) := by
  classical
  let pf := betaParams (phaseBoxCoupling phaseJ a R) beta
  have hpf : forall e, 0 < pf e :=
    betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta
  have hpf1 : forall e, pf e < 1 := betaParams_lt_one _ beta
  have hparam : forall e, pf e <= p := by
    intro e
    have hcoupling : phaseJ a (Sym2.map Subtype.val e) <= Jmax := hJhi _
    have hexp : Real.exp (-(beta * Jmax)) <=
        Real.exp (-(beta * phaseJ a (Sym2.map Subtype.val e))) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    exact (by
      unfold pf betaParams phaseBoxCoupling boxCoupling
      linarith : pf e <= 1 - Real.exp (-(beta * Jmax))).trans hpmax
  have hmono := FK.bcProbW_mono_params
    (boxGraph d R) (WiredBoxDifferential.wiredBoxBoundaryGraph d R)
    (pf1 := pf) (pf2 := fun _ => p)
    hpf hpf1 (fun _ => hp) (fun _ => hp1) hparam hq
    (isIncreasing_connToBdryEventLE d hkR)
  calc
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) =
        ∑ omega, (connToBdryEventLE d hkR).indicator
            (fun _ => (1 : Real)) omega *
          bcProbW (boxGraph d R)
            (WiredBoxDifferential.wiredBoxBoundaryGraph d R) pf q omega := by
      exact weightedPhaseFiniteMeasure_shell_eq
        d hkR phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
    _ <= ∑ omega, (connToBdryEventLE d hkR).indicator
          (fun _ => (1 : Real)) omega *
        bcProbW (boxGraph d R)
          (WiredBoxDifferential.wiredBoxBoundaryGraph d R)
          (fun _ => p) q omega := hmono
    _ = (wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k) := by
      rw [boxBdryConnEvent_eq_boxRestrict_preimage d hkR,
        fkgq_wiredFiniteMeasure_real_boxRestrictEvent R hp hp1
          (zero_lt_one.trans_le hq) (connToBdryEventLE d hkR)
          (measurableSet_boxRestrict_connToBdryEventLE d hkR)]
      apply Finset.sum_congr rfl
      intro omega homega
      rw [FK.bcProbW_const]
      change _ * bcProb (boxGraph d R)
          (boundaryCliqueGraph (boxBoundary d R)) p q omega = _
      rw [bcProb_clique_eq_wiredFkProb]


theorem weightedPhaseInfiniteTheta_le_fkTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e)
    (Jmax : Real) (hJhi : forall e, phaseJ a e <= Jmax)
    (q beta p : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hp : 0 < p) (hp1 : p < 1)
    (hpmax : 1 - Real.exp (-(beta * Jmax)) <= p) :
    weightedPhaseInfiniteTheta d phaseJ a hJ q beta
        (zero_lt_one.trans_le hq) hbeta <=
      fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) := by
  classical
  let muW := fun R =>
    ((weightedPhaseFiniteMeasure d R phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let muH := fun R =>
    ((wiredFiniteMeasure d R hp hp1 (zero_lt_one.trans_le hq) :
      ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d))))
  have hshell : forall k,
      weightedPhaseInfiniteShell d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta k <=
        ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k) := by
    intro k
    obtain ⟨phi, hphi, hweighted⟩ :=
      weightedPhaseFiniteShell_tendsto_infinite
        d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
    let A : Set (ConfigSpace (Sym2 (boxVerts d k))) :=
      {omega | IsingFK.ConnToBdry (boxGraph d k) (boxBoundary d k) omega
        (IsingFK.boxOrigin d k)}
    have hhomRaw := (fkgq_wired_infinite_measure k hp hp1 hq
      (S := A) (isIncreasing_connToBdryEvent k)).comp hphi.tendsto_atTop
    have hAeq : boxRestrict d k ⁻¹' A = boxBdryConnEvent d k := rfl
    rw [hAeq] at hhomRaw
    have hhom : Tendsto
        (fun n => (muH (phi n)).real (boxBdryConnEvent d k)) atTop
        (nhds (((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
          ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
            (boxBdryConnEvent d k))) := by
      simpa [muH, Function.comp_def] using hhomRaw
    have hweighted' : Tendsto
        (fun n => (muW (phi n)).real (boxBdryConnEvent d k)) atTop
        (nhds (weightedPhaseInfiniteShell d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta k)) := by
      simpa [muW] using hweighted k
    apply le_of_tendsto_of_tendsto hweighted' hhom
    filter_upwards [hphi.tendsto_atTop.eventually (eventually_ge_atTop k)]
      with n hkn
    exact weightedPhaseFinite_shell_le_wiredFinite
      d k (phi n) hkn phaseJ a hJ Jmax hJhi q beta p hq hbeta
        hp hp1 hpmax
  have hweightedTheta := weightedPhaseInfiniteShell_tendsto_theta
    d phaseJ a hJ q beta (zero_lt_one.trans_le hq) hbeta
  have hhomTheta : Tendsto
      (fun k => ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d)))).real
          (boxBdryConnEvent d k)) atTop
      (nhds (fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q))) := by
    exact boxBdryConnEvent_real_tendsto_percolation
      ((wiredInfiniteVolume d hp hp1 (zero_lt_one.trans_le hq) :
        ProbabilityMeasure _) : Measure (ConfigSpace (Sym2 (Site d))))
  exact le_of_tendsto_of_tendsto hweightedTheta hhomTheta
    (Eventually.of_forall hshell)


theorem phaseCoupling_upper
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (hsurj : Function.Surjective phase)
    {Jmax : Real} (hJhi : forall e, J e <= Jmax) :
    forall a e, phaseJ a e <= Jmax := by
  intro a e
  obtain ⟨x, rfl⟩ := hsurj a
  rw [← hcov x e]
  exact hJhi _


theorem weightedThreshold_pos_of_highBetaWitness
    (d : Nat) (hd : 2 <= d)
    {P : Type*} [Fintype P] [Nonempty P]
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
    0 < beta1 (fun b n => Sig
      (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b) := by
  classical
  let hpPhase := hcov.phaseCoupling_pos hsurj
    (fun e => hJmin.trans_le (hJlo e))
  let betaOne := beta1 (fun b n => Sig
    (weightedThresholdPhaseSum d phaseJ Jmin Jmax q beta0) n b)
  obtain ⟨betaStar, hbetaStar, hstar0, hstar⟩ := hhigh
  have hbeta0 : 0 < beta0 := hbetaStar.trans hstar0
  have hJmax : 0 < Jmax := by
    let e : Sym2 (Site d) := s((0 : Site d), (0 : Site d))
    exact hJmin.trans_le (hJlo e) |>.trans_le (hJhi e)
  let p : Real := 1 / (4 * d)
  have hdpos : (0 : Real) < d := by exact_mod_cast (by omega : 0 < d)
  have hdTwo : (2 : Real) <= d := by exact_mod_cast hd
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hp1 : p < 1 := by
    dsimp [p]
    rw [div_lt_one (by positivity)]
    nlinarith [hdTwo]
  have hsmall : (2 * d : Real) * p < 1 := by
    dsimp [p]
    rw [mul_one_div, div_lt_one (by positivity)]
    nlinarith [hdTwo]
  let betaSmall := -Real.log (1 - p) / Jmax
  have hremain : 0 < 1 - p := sub_pos.mpr hp1
  have hremain1 : 1 - p < 1 := by linarith
  have hbetaSmall : 0 < betaSmall := by
    dsimp [betaSmall]
    exact div_pos (neg_pos.mpr (Real.log_neg hremain hremain1)) hJmax
  let betaLow := min betaSmall (beta0 / 2)
  have hbetaLow : 0 < betaLow := by
    dsimp [betaLow]
    exact lt_min hbetaSmall (half_pos hbeta0)
  have hlow0 : betaLow <= beta0 := by
    have hle : betaLow <= beta0 / 2 := min_le_right _ _
    linarith
  have hpmax : 1 - Real.exp (-(betaLow * Jmax)) <= p := by
    have hmul : betaSmall * Jmax = -Real.log (1 - p) := by
      dsimp [betaSmall]
      field_simp
    have hparamSmall : 1 - Real.exp (-(betaSmall * Jmax)) = p := by
      rw [hmul, neg_neg, Real.exp_log hremain]
      ring
    have hprod : betaLow * Jmax <= betaSmall * Jmax :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hJmax.le
    have hexp : Real.exp (-(betaSmall * Jmax)) <=
        Real.exp (-(betaLow * Jmax)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hprod)
    linarith
  have hphaseHi : forall a e, phaseJ a e <= Jmax :=
    phaseCoupling_upper hcov hsurj hJhi
  have hthetaHom : fkTheta d hp hp1 (zero_lt_one.trans_le hq) (q := q) = 0 :=
    FK.fkTheta_eq_zero_of_lt (by omega) hp hp1 hq hsmall
  have hphaseZero : forall a,
      weightedPhaseThetaProfile d phaseJ hpPhase q
        (zero_lt_one.trans_le hq) a betaLow = 0 := by
    intro a
    unfold weightedPhaseThetaProfile
    rw [dif_pos hbetaLow]
    apply le_antisymm
    · exact (weightedPhaseInfiniteTheta_le_fkTheta
        d phaseJ a (hpPhase a) Jmax (hphaseHi a)
          q betaLow p hq hbetaLow hp hp1 hpmax).trans_eq hthetaHom
    · exact weightedPhaseInfiniteTheta_nonneg
        d phaseJ a (hpPhase a) q betaLow
          (zero_lt_one.trans_le hq) hbetaLow
  have hsumZero : weightedSelectedPhaseSum d phaseJ hpPhase q
      (zero_lt_one.trans_le hq) betaLow = 0 := by
    unfold weightedSelectedPhaseSum
    exact Finset.sum_eq_zero fun a ha => hphaseZero a
  have hne := weightedHighBetaWitness_threshold_nonempty
    d phaseJ hpPhase Jmin Jmax q beta0 hJmin hq
      (by simpa [hpPhase] using
        (⟨betaStar, hbetaStar, hstar0, hstar⟩ :
          weightedSelectedPhaseHighBetaWitness d phaseJ hpPhase q
            (zero_lt_one.trans_le hq) beta0))
  by_contra hnot
  have hbetaOneLow : betaOne < betaLow :=
    lt_of_le_of_lt (not_lt.mp hnot) hbetaLow
  have hmf := weightedSelectedPhaseSum_meanField_lower
    d J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta0 betaLow hq hne hbetaOneLow hlow0
  have hfactor : 0 < weightedPhaseSharpConstant d Jmin Jmax beta0 *
      (betaLow - betaOne) :=
    mul_pos (weightedPhaseSharpConstant_pos d hJmin)
      (sub_pos.mpr hbetaOneLow)
  have hsumPos : 0 < weightedSelectedPhaseSum d phaseJ hpPhase q
      (zero_lt_one.trans_le hq) betaLow := hfactor.trans_le (by
        simpa [hpPhase, betaOne] using hmf)
  rw [hsumZero] at hsumPos
  exact lt_irrefl 0 hsumPos


theorem weightedPhaseInfinite_singleOpen_measurable_bound
    (d N : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (hJ : forall e, 0 < phaseJ a e) (q beta : Real)
    (hq : 1 <= q) (hbeta : 0 < beta)
    (eN : (boxGraph d N).edgeSet)
    (A : Set (ConfigSpace (Sym2 (Site d)))) (hA : MeasurableSet A) :
    weightedOpenTolerance
        (betaParams (phaseJ a) beta (WiredBoxDifferential.boxActiveEdge d N eN)) q *
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
          Measure (ConfigSpace (Sym2 (Site d)))).real
        (setOpen (WiredBoxDifferential.boxActiveEdge d N eN) ⁻¹' A) <=
      ((weightedPhaseInfiniteVolume d phaseJ a hJ q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
          Measure (ConfigSpace (Sym2 (Site d)))).real A := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) :=
    weightedPhaseInfiniteVolume d phaseJ a hJ q beta
      (zero_lt_one.trans_le hq) hbeta
  let p := betaParams (phaseJ a) beta
    (WiredBoxDifferential.boxActiveEdge d N eN)
  have hp : 0 < p := by
    dsimp [p, betaParams]
    have hprod := mul_pos hbeta
      (hJ (WiredBoxDifferential.boxActiveEdge d N eN))
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hprod)
    linarith
  have hp1 : p < 1 := by
    dsimp [p, betaParams]
    linarith [Real.exp_pos
      (-(beta * phaseJ a (WiredBoxDifferential.boxActiveEdge d N eN)))]
  exact pattern_bound_of_cylinders mu
    (setOpen (WiredBoxDifferential.boxActiveEdge d N eN))
    (measurable_setOpen _) (weightedOpenTolerance p q)
    (weightedOpenTolerance_pos hp hp1 hq).le
    (weightedPhaseInfinite_singleOpen_fullCylinder_bound
      d N phaseJ a hJ q beta hq hbeta eN) A hA


theorem div_q_le_weightedOpenTolerance
    {p0 p q : Real} (hp0p : p0 <= p)
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    p0 / q <= weightedOpenTolerance p q := by
  have hqpos : 0 < q := zero_lt_one.trans_le hq
  have hdenpos : 0 < p + q * (1 - p) :=
    add_pos hp (mul_pos hqpos (sub_pos.mpr hp1))
  have hdenle : p + q * (1 - p) <= q := by
    have hmul : 0 <= p * (q - 1) :=
      mul_nonneg hp.le (sub_nonneg.mpr hq)
    nlinarith
  unfold weightedOpenTolerance
  apply (div_le_div_iff₀ hqpos hdenpos).2
  calc
    p0 * (p + q * (1 - p)) <= p * (p + q * (1 - p)) :=
      mul_le_mul_of_nonneg_right hp0p hdenpos.le
    _ <= p * q := mul_le_mul_of_nonneg_left hdenle hp.le


end FKSharpnessWeightedPhasewiseMeanField
end OSSS
end StatMech
