/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedLocalized
open scoped BigOperators Classical
open Finset Set
open MeasureTheory


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedIntegration

open Lattice FK RevealmentConstruction AdaptiveCovLowerGeom

open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre

open ActiveBoundaryDifferential ActiveEdgeDifferential

open FKSharpnessWeightedPeriodic FKSharpnessWeightedStrict

open FKSharpnessWeightedLocalized

open FKSharpnessWeightedInfiniteVolume

open FKSharpnessWeightedCoherentLimit


theorem weightedLocalizedTheta_one_sub_lower
    (d n : Nat)
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax q beta beta0 : Real)
    (hJmin : 0 < Jmin) (hJlo : forall e, Jmin <= J e)
    (hJhi : forall e, J e <= Jmax)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    Real.exp (-(beta0 * Jmax)) ^ (2 * d) <=
      1 - weightedLocalizedTheta d n J q beta := by
  let G := boxGraph d (2 * n)
  let C := wiredBoxBoundaryGraph d (2 * n)
  let Jbox := boxCoupling J (2 * n)
  let mu := activeBCProb G C (betaParams Jbox beta) q
  let full := crossIndG (boxActiveEdge d (2 * n)) 0 n
  let I := incidentEdges (boxActiveEndU d (2 * n))
    (boxActiveEndV d (2 * n)) 0
  have hJbox : forall e, 0 < Jbox e := fun e =>
    hJmin.trans_le (hJlo (Sym2.map Subtype.val e))
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq0 omega).le
  have hoB : (0 : Site d) ∉ vertexBoundary d n := by
    intro h
    apply origin_not_mem_osssBoundaryFinset d n
    rw [mem_osssBoundaryFinset]
    exact h
  have hfull := activeBC_cross_one_sub_lower G C Jbox hJbox
    q beta beta0 hq hbeta hbeta0
    (boxActiveEdge_eq_endpoints d (2 * n))
    (0 : Site d) (vertexBoundary d n) hoB
  have hfull' : I.prod (fun e => Real.exp (-(beta0 * Jbox e.1))) <=
      1 - Lindeberg.mean mu full := by
    simpa [G, C, Jbox, mu, full, I] using hfull
  have hmean : Lindeberg.mean mu (innerCrossInd d n) <=
      Lindeberg.mean mu full := by
    unfold Lindeberg.mean
    apply Finset.sum_le_sum
    intro omega homega
    apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
    exact innerCrossInd_le_fullOuterCrossInd d n omega
  have hbeta0pos : 0 < beta0 := hbeta.trans_le hbeta0
  have hJmax : 0 < Jmax := by
    let e0 : Sym2 (Site d) := s(0, 0)
    exact (hJmin.trans_le (hJlo e0)).trans_le (hJhi e0)
  have hkbase0 : 0 < Real.exp (-(beta0 * Jmax)) := Real.exp_pos _
  have hkbase1 : Real.exp (-(beta0 * Jmax)) <= 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hbeta0pos hJmax])
  have hkpow : Real.exp (-(beta0 * Jmax)) ^ (2 * d) <=
      Real.exp (-(beta0 * Jmax)) ^ I.card := by
    exact pow_le_pow_of_le_one hkbase0.le hkbase1
      (wiredOuterIncident_card_le d (2 * n))
  have hterm : forall e, e ∈ I ->
      Real.exp (-(beta0 * Jmax)) <=
        Real.exp (-(beta0 * Jbox e.1)) := by
    intro e he
    apply Real.exp_le_exp.mpr
    have hle := hJhi (Sym2.map Subtype.val e.1)
    dsimp [Jbox, boxCoupling]
    nlinarith
  have hkprod : Real.exp (-(beta0 * Jmax)) ^ (2 * d) <=
      I.prod (fun e => Real.exp (-(beta0 * Jbox e.1))) :=
    hkpow.trans (by
      simpa [Finset.prod_const] using Finset.prod_le_prod
        (fun e he => hkbase0.le) hterm)
  exact hkprod.trans (hfull'.trans (by
    simpa [weightedLocalizedTheta, G, C, Jbox, mu, full] using
      sub_le_sub_left hmean 1))


theorem weighted_outer_inner_differential_absorbed
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
    Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) *
        (weightedLocalizedTheta d n J q beta /
          (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (wiredBoxBoundaryGraph d (2 * n))
        (betaParams (boxCoupling J (2 * n)) b) q
        (innerCrossInd d n)) beta := by
  let theta := weightedLocalizedTheta d n J q beta
  let D := 8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real)
  let kappa := Real.exp (-(beta0 * Jmax)) ^ (2 * d)
  have htheta : 0 <= theta := weightedLocalizedTheta_nonneg
    d n J (fun e => hJmin.trans_le (hJlo e)) q beta hq hbeta
  have hstrict := weightedStrictDenom_pos d n hn J
    (fun e => hJmin.trans_le (hJlo e)) q beta hq hbeta
  have hdenle := weightedStrictDenom_le_phaseEnvelopeSig
    d n J (fun e => hJmin.trans_le (hJlo e)) phase phaseJ hsurj hcov
      q beta hq hbeta
  have hD : 0 < D := hstrict.trans_le (by simpa [D] using hdenle)
  have hkappa : 0 < kappa := by unfold kappa; positivity
  have hgap : kappa <= 1 - theta := by
    simpa [kappa, theta] using weightedLocalizedTheta_one_sub_lower
      d n J Jmin Jmax q beta beta0 hJmin hJlo hJhi hq hbeta hbeta0
  have hlog : Jmin * (theta * (1 - theta) / D) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (wiredBoxBoundaryGraph d (2 * n))
        (betaParams (boxCoupling J (2 * n)) b) q
        (innerCrossInd d n)) beta := by
    simpa [theta, D] using
      weighted_outer_inner_differential_phaseEnvelope_uniform
        d n hn J Jmin hJmin hJlo phase phaseJ hsurj hcov
        q beta hq hbeta
  obtain ⟨_, hmain⟩ := absorb_cross_complement
    htheta hD hkappa hJmin hgap hlog
  simpa [theta, D, kappa, mul_assoc] using hmain


theorem weighted_outer_inner_differential_integration
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
    (Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8) *
        (((n : Real) / weightedPhaseEnvelopeSig d n phaseJ q beta) *
          weightedLocalizedTheta d n J q beta) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (wiredBoxBoundaryGraph d (2 * n))
        (betaParams (boxCoupling J (2 * n)) b) q
        (innerCrossInd d n)) beta := by
  have hmain := weighted_outer_inner_differential_absorbed
    d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
      q beta beta0 hq hbeta hbeta0
  let S := weightedPhaseEnvelopeSig d n phaseJ q beta
  have hnR : (0 : Real) < n := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hstrict := weightedStrictDenom_pos d n hn J
    (fun e => hJmin.trans_le (hJlo e)) q beta hq hbeta
  have hdenle := weightedStrictDenom_le_phaseEnvelopeSig
    d n J (fun e => hJmin.trans_le (hJlo e)) phase phaseJ hsurj hcov
      q beta hq hbeta
  have hD : 0 < 8 * S / (n : Real) :=
    hstrict.trans_le (by simpa [S] using hdenle)
  have hS : 0 < S := by
    rcases (div_pos_iff.mp hD) with h | h
    · nlinarith
    · linarith
  convert hmain using 1
  field_simp


theorem weightedLocalizedTheta_eq_phaseProfile_origin
    (d n : Nat) (hn : 1 <= n)
    {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta : Real) :
    weightedLocalizedTheta d n J q beta =
      weightedPhaseProfile d phaseJ (phase 0) q beta n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [weightedPhaseProfile, if_neg hn0]
  unfold weightedLocalizedTheta weightedPhaseWiredTheta
  have hcoupling : phaseBoxCoupling phaseJ (phase 0) (2 * n) =
      boxCoupling J (2 * n) := by
    funext e
    unfold phaseBoxCoupling boxCoupling
    have hc := hcov 0 (Sym2.map Subtype.val e)
    simpa [translateAmbientEdge] using hc.symm
  rw [hcoupling]


theorem weightedPhaseProfile_differential_integration
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta beta0 : Real) (hq : 1 <= q)
    (hbeta : 0 < beta) (hbeta0 : beta <= beta0)
    (x : Site d) :
    (Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8) *
        (((n : Real) / weightedPhaseEnvelopeSig d n phaseJ q beta) *
          weightedPhaseProfile d phaseJ (phase x) q beta n) <=
      deriv (fun b => weightedPhaseProfile d phaseJ (phase x) q b n) beta := by
  let K : Sym2 (Site d) -> Real := phaseJ (phase x)
  let phaseX : Site d -> P := fun z => phase (z + x)
  have hcovX : PhaseCovariant K phaseX phaseJ := by
    intro z e
    have hc :=
      FKSharpnessWeightedInfiniteVolume.PhaseCovariant.phaseCoupling_translate
        hcov x (z + x) e
    have hsub : z + x - x = z := by abel
    simpa [K, phaseX, hsub] using hc.symm
  have hsurjX : Function.Surjective phaseX := by
    intro a
    obtain ⟨y, hy⟩ := hsurj a
    refine ⟨y - x, ?_⟩
    simpa [phaseX, sub_add_cancel] using hy
  have hKlo : forall e, Jmin <= K e := by
    intro e
    have hc := hcov x e
    change Jmin <= phaseJ (phase x) e
    rw [← hc]
    exact hJlo _
  have hKhi : forall e, K e <= Jmax := by
    intro e
    have hc := hcov x e
    change phaseJ (phase x) e <= Jmax
    rw [← hc]
    exact hJhi _
  have hmain := weighted_outer_inner_differential_integration
    d n hn K Jmin Jmax hJmin hKlo hKhi phaseX phaseJ hsurjX hcovX
      q beta beta0 hq hbeta hbeta0
  have horigin : phaseX 0 = phase x := by simp [phaseX]
  have htheta := weightedLocalizedTheta_eq_phaseProfile_origin
    d n hn K phaseX phaseJ hcovX q beta
  have hfun : (fun b => activeBCMean (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (betaParams (boxCoupling K (2 * n)) b) q
      (innerCrossInd d n)) =
      (fun b => weightedPhaseProfile d phaseJ (phase x) q b n) := by
    funext b
    have hb := weightedLocalizedTheta_eq_phaseProfile_origin
      d n hn K phaseX phaseJ hcovX q b
    simpa [weightedLocalizedTheta, horigin] using hb
  rw [hfun] at hmain
  rw [htheta, horigin] at hmain
  exact hmain


end FKSharpnessWeightedIntegration
end OSSS
end StatMech
