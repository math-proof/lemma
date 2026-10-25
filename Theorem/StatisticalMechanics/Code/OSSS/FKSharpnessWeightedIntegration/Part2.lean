/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedLocalized
import Def.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedIntegration
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


theorem weightedPhaseProfile_differentiableAt
    (d n : Nat) (hn : 1 <= n) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    DifferentiableAt Real (fun b => weightedPhaseProfile d phaseJ a q b n) beta := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp only [weightedPhaseProfile, if_neg hn0]
  unfold weightedPhaseWiredTheta
  exact (hasDerivAt_activeBCMean_beta_sum
    (boxGraph d (2 * n)) (wiredBoxBoundaryGraph d (2 * n))
    (fun e => hJ a (Sym2.map Subtype.val e)) hbeta
    (zero_lt_one.trans_le hq) (innerCrossInd d n)).differentiableAt

theorem weightedPhaseEnvelopeSig_le_sumSig
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedPhaseEnvelopeSig d n phaseJ q beta <=
      weightedPhaseSumSig d n phaseJ q beta := by
  unfold weightedPhaseEnvelopeSig weightedPhaseSumSig weightedPhaseSum
  apply Finset.sum_le_sum
  intro k hk
  apply Finset.sup'_le Finset.univ_nonempty
  intro a ha
  exact Finset.single_le_sum
    (fun b hb => weightedPhaseProfile_nonneg d phaseJ hJ b q beta hq hbeta k)
    (Finset.mem_univ a)


theorem weightedPhaseSum_differential_integration
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
        (((n : Real) / weightedPhaseSumSig d n phaseJ q beta) *
          weightedPhaseSum d phaseJ q beta n) <=
      deriv (fun b => weightedPhaseSum d phaseJ q b n) beta := by
  let c := Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) / 8
  let E := weightedPhaseEnvelopeSig d n phaseJ q beta
  let S := weightedPhaseSumSig d n phaseJ q beta
  let F := weightedPhaseSum d phaseJ q beta n
  have hp : forall a e, 0 < phaseJ a e :=
    hcov.phaseCoupling_pos hsurj (fun e => hJmin.trans_le (hJlo e))
  have hc : 0 < c := by unfold c; positivity
  have hEpos : 0 < E := by
    have hstrict := weightedStrictDenom_pos d n hn J
      (fun e => hJmin.trans_le (hJlo e)) q beta hq hbeta
    have hle := weightedStrictDenom_le_phaseEnvelopeSig
      d n J (fun e => hJmin.trans_le (hJlo e)) phase phaseJ hsurj hcov
        q beta hq hbeta
    have hnR : (0 : Real) < n := by exact_mod_cast
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
    have hD : 0 < 8 * E / (n : Real) := hstrict.trans_le (by
      simpa [E] using hle)
    rcases (div_pos_iff.mp hD) with h | h
    · nlinarith
    · linarith
  have hES : E <= S := weightedPhaseEnvelopeSig_le_sumSig
    d n phaseJ hp q beta hq hbeta
  have hSpos : 0 < S := hEpos.trans_le hES
  have hF0 : 0 <= F := by
    unfold F weightedPhaseSum
    exact Finset.sum_nonneg fun a ha =>
      weightedPhaseProfile_nonneg d phaseJ hp a q beta hq hbeta n
  have hratio : ((n : Real) / S) * F <= ((n : Real) / E) * F := by
    apply mul_le_mul_of_nonneg_right _ hF0
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) hEpos hES
  have hphase : forall a : P,
      c * (((n : Real) / E) * weightedPhaseProfile d phaseJ a q beta n) <=
        deriv (fun b => weightedPhaseProfile d phaseJ a q b n) beta := by
    intro a
    obtain ⟨x, hx⟩ := hsurj a
    subst a
    exact weightedPhaseProfile_differential_integration
      d n hn J Jmin Jmax hJmin hJlo hJhi phase phaseJ hsurj hcov
        q beta beta0 hq hbeta hbeta0 x
  have hsum : c * (((n : Real) / E) * F) <=
      ∑ a : P, deriv (fun b => weightedPhaseProfile d phaseJ a q b n) beta := by
    unfold F weightedPhaseSum
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun a ha => hphase a
  have hderiv : deriv (fun b => weightedPhaseSum d phaseJ q b n) beta =
      ∑ a : P, deriv (fun b => weightedPhaseProfile d phaseJ a q b n) beta := by
    have hsumDeriv := HasDerivAt.sum fun a
        (_ : a ∈ (Finset.univ : Finset P)) =>
      (weightedPhaseProfile_differentiableAt
        d n hn phaseJ hp a q beta hq hbeta).hasDerivAt
    have heq : (∑ a : P, fun b => weightedPhaseProfile d phaseJ a q b n) =
        (fun b => weightedPhaseSum d phaseJ q b n) := by
      funext b
      rw [Finset.sum_apply]
      rfl
    rw [heq] at hsumDeriv
    exact hsumDeriv.deriv
  rw [hderiv]
  exact (mul_le_mul_of_nonneg_left hratio hc.le).trans hsum


theorem weightedPhasePhysical_le_localized_half
    (d n : Nat) (hn : 2 <= n) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    ((weightedPhaseFiniteMeasure d n phaseJ a (hJ a) q beta
        (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
      Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxBdryConnEvent d n) <=
      weightedPhaseProfile d phaseJ a q beta (n / 2) := by
  let k := n / 2
  have hk : 1 <= k := by dsimp [k]; omega
  have hkn : 2 * k <= n := by dsimp [k]; omega
  have hevent : boxBdryConnEvent d n ⊆ boxBdryConnEvent d k :=
    boxBdryConnEvent_subset_le k n hk (by omega)
  have hsame :
      ((weightedPhaseFiniteMeasure d n phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d n) <=
      ((weightedPhaseFiniteMeasure d n phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d k) :=
    measureReal_mono hevent (measure_ne_top _ _)
  have hdomain :
      ((weightedPhaseFiniteMeasure d n phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d k) <=
      ((weightedPhaseFiniteMeasure d (2 * k) phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d k) := by
    by_cases heq : 2 * k = n
    · rw [← heq]
    · exact weightedPhaseFiniteMeasure_shell_mono d hk
        (n_le_two_mul k) (lt_of_le_of_ne hkn heq) phaseJ a (hJ a)
        q beta hq hbeta
  calc
    _ <= ((weightedPhaseFiniteMeasure d n phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d k) := hsame
    _ <= ((weightedPhaseFiniteMeasure d (2 * k) phaseJ a (hJ a) q beta
          (zero_lt_one.trans_le hq) hbeta : ProbabilityMeasure _) :
        Measure _).real (boxBdryConnEvent d k) := hdomain
    _ = weightedPhaseWiredTheta d phaseJ a q beta k :=
      (weightedPhaseWiredTheta_eq_finiteMeasure_double
        d k hk phaseJ a (hJ a) q beta hq hbeta).symm
    _ = weightedPhaseProfile d phaseJ a q beta k := by
      symm
      simp [weightedPhaseProfile, Nat.ne_of_gt hk]

end FKSharpnessWeightedIntegration
end OSSS
end StatMech
