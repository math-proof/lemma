/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle
open Finset Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheL_phase_ne_zero
    {c : Real} (hc : 2 < c) (y : Real) :
    sixVertexBetheL c (sixVertexBethePhase y) ≠ 0 := by
  rw [sixVertexBetheL_phase_eq_conj_M]
  exact star_ne_zero.mpr (sixVertexBetheM_phase_ne_zero hc y)

theorem sixVertexTheta_zero_exp_neg_eq_neg_M_div_L
    {c : Real} (hc : 2 < c) {y : Real}
    (hy : sixVertexBethePhase y ≠ 1) :
    Complex.exp (-Complex.I * sixVertexTheta c 0 y) =
      -sixVertexBetheM c (sixVertexBethePhase y) /
        sixVertexBetheL c (sixVertexBethePhase y) := by
  have hpos := sixVertexTheta_zero_exp_eq_neg_L_div_M hc hy
  have hmul : Complex.exp (-Complex.I * sixVertexTheta c 0 y) *
      Complex.exp (Complex.I * sixVertexTheta c 0 y) = 1 := by
    rw [← Complex.exp_add]
    ring_nf
    simp
  rw [hpos] at hmul
  apply (eq_div_iff (sixVertexBetheL_phase_ne_zero hc y)).2
  have hM := sixVertexBetheM_phase_ne_zero hc y
  field_simp [hM] at hmul ⊢
  linear_combination -hmul

theorem sixVertexBetheZeroDerivative_algebra
    {c : Real} (hc : 2 < c) {y : Real}
    (hy : sixVertexBethePhase y ≠ 1) :
    sixVertexBetheM c (sixVertexBethePhase y) *
          ((2 : Complex) - (c : Complex) ^ 2) - 1 -
        sixVertexBetheM c (sixVertexBethePhase y) /
          sixVertexBetheL c (sixVertexBethePhase y) =
      sixVertexBetheM c (sixVertexBethePhase y) *
        (c : Complex) ^ 2 * sixVertexThetaLeftDerivAtZero c y := by
  have hyden : 1 - sixVertexBethePhase y ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hy)
  have hL := sixVertexBetheL_phase_ne_zero hc y
  have hderiv : sixVertexThetaLeftDerivAtZero c y =
      4 * ((2 - c ^ 2) / 2) * (Real.cos y - (2 - c ^ 2) / 2) /
        ((1 + Real.cos y - 2 * ((2 - c ^ 2) / 2)) ^ 2 +
          Real.sin y ^ 2) := by
    unfold sixVertexThetaLeftDerivAtZero sixVertexBetheIntegratingFactor
      sixVertexThetaDerivativeDenominator sixVertexThetaDenominator
      sixVertexDelta
    simp [pow_two]
  have hrealden :
      (1 + Real.cos y - 2 * ((2 - c ^ 2) / 2)) ^ 2 +
        Real.sin y ^ 2 ≠ 0 := by
    have hpos := sixVertexThetaDerivativeDenominator_pos hc 0 y
    simpa [sixVertexThetaDerivativeDenominator,
      sixVertexThetaDenominator, sixVertexDelta, pow_two] using hpos.ne'
  have hrealden' :
      (1 + Real.cos y - (2 - c ^ 2)) ^ 2 + Real.sin y ^ 2 ≠ 0 := by
    convert hrealden using 1 <;> ring
  let D : Real := c ^ 4 + 2 * c ^ 2 * Real.cos y - 2 * c ^ 2 -
    2 * Real.cos y + 2
  have hdeneq :
      (1 + Real.cos y - (2 - c ^ 2)) ^ 2 + Real.sin y ^ 2 = D := by
    dsimp [D]
    nlinarith [Real.sin_sq_add_cos_sq y]
  have hD : D ≠ 0 := by rwa [← hdeneq]
  have hderiv' : sixVertexThetaLeftDerivAtZero c y =
      -(c ^ 2 - 2) * (c ^ 2 + 2 * Real.cos y - 2) / D := by
    rw [hderiv]
    rw [show (1 + Real.cos y - 2 * ((2 - c ^ 2) / 2)) ^ 2 +
        Real.sin y ^ 2 = D by
          rw [show 2 * ((2 - c ^ 2) / 2) = 2 - c ^ 2 by ring]
          exact hdeneq]
    ring
  have hquad : sixVertexBethePhase y ^ 2 -
      2 * (Real.cos y : Complex) * sixVertexBethePhase y + 1 = 0 := by
    have hphase : sixVertexBethePhase y =
        (Real.cos y : Complex) + (Real.sin y : Complex) * Complex.I := by
      unfold sixVertexBethePhase
      rw [show Complex.I * (y : Complex) = (y : Complex) * Complex.I by ring,
        Complex.exp_ofReal_mul_I]
    rw [hphase]
    ring_nf
    rw [Complex.I_sq]
    have htrig : ((Real.sin y : Complex) ^ 2 +
        (Real.cos y : Complex) ^ 2) = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq y
    linear_combination -htrig
  rw [hderiv']
  field_simp [hL]
  unfold sixVertexBetheL sixVertexBetheM
  have hDC : (D : Complex) ≠ 0 := Complex.ofReal_ne_zero.mpr hD
  push_cast
  rw [← Complex.ofReal_cos]
  field_simp [hyden, hDC]
  dsimp [D]
  push_cast
  rw [← Complex.ofReal_cos]
  linear_combination
    ((c : Complex) ^ 4 * ((c : Complex) ^ 2 - 2)) * hquad


theorem sixVertexBetheZeroAdjacentPairFactor_eq_deriv
    {c : Real} (hc : 2 < c) {y eps : Real}
    (hy : sixVertexBethePhase y ≠ 1)
    (heps : sixVertexBethePhase eps ≠ 1) :
    (sixVertexBetheM c (sixVertexBethePhase y) *
          sixVertexBetheL c (sixVertexBethePhase eps) - 1) -
      Complex.exp (-Complex.I * sixVertexTheta c 0 y) *
        (sixVertexBetheM c (sixVertexBethePhase eps) *
          sixVertexBetheL c (sixVertexBethePhase y) - 1) =
      (c : Complex) ^ 2 * sixVertexBetheM c (sixVertexBethePhase y) *
        sixVertexThetaLeftDerivAtZero c y := by
  rw [sixVertexTheta_zero_exp_neg_eq_neg_M_div_L hc hy]
  calc
    _ = sixVertexBetheM c (sixVertexBethePhase y) *
          (sixVertexBetheL c (sixVertexBethePhase eps) +
            sixVertexBetheM c (sixVertexBethePhase eps)) - 1 -
          sixVertexBetheM c (sixVertexBethePhase y) /
            sixVertexBetheL c (sixVertexBethePhase y) := by
      field_simp [sixVertexBetheL_phase_ne_zero hc y]
      ring
    _ = sixVertexBetheM c (sixVertexBethePhase y) *
          ((2 : Complex) - (c : Complex) ^ 2) - 1 -
          sixVertexBetheM c (sixVertexBethePhase y) /
            sixVertexBetheL c (sixVertexBethePhase y) := by
      rw [sixVertexBetheL_add_M heps]
    _ = _ := by
      rw [sixVertexBetheZeroDerivative_algebra hc hy]
      ring


theorem sixVertexBethePerturbedWordTerm_adjacent_zero_pair
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 1) → Real) (ell : Fin (n + 1)) (hell : p ell = 0)
    (eps : Real) (heps : sixVertexBethePhase eps ≠ 1)
    (x : Fin (n + 1) → Int) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (sigma : Equiv.Perm (Fin (n + 1))) (hzero : sigma i.succ = ell)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
        sixVertexBethePerturbedWordTerm N c p ell eps x w
          (sigma * Equiv.swap i.castSucc i.succ) =
      (c : Complex) ^ 2 *
        sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) *
        sixVertexBetheM c (sixVertexBethePhase (p (sigma i.castSucc))) *
        sixVertexBetheAmplitude c p sigma *
        sixVertexBetheWordCoefficientRemainder c
          (fun j => sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps j)) sigma w i.castSucc *
        sixVertexBetheWordMonomial N
          (fun j => sixVertexBethePhase
            (sixVertexBethePerturbRoot p ell eps j)) sigma x w := by
  let z : Fin (n + 1) → Complex := fun j => sixVertexBethePhase
    (sixVertexBethePerturbRoot p ell eps j)
  let a : Fin (n + 1) := i.castSucc
  let b : Fin (n + 1) := i.succ
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hleft : sigma a ≠ ell := by
    intro h
    apply hab
    exact sigma.injective (h.trans hzero.symm)
  have hza : z (sigma a) = sixVertexBethePhase (p (sigma a)) := by
    simp [z, sixVertexBethePerturbRoot, hleft]
  have hzb : z (sigma b) = sixVertexBethePhase eps := by
    dsimp [b]
    rw [hzero]
    simp [z]
  have hphase : sixVertexBethePhase (p (sigma a)) ≠ 1 :=
    hother _ hleft
  have hamp0 := sixVertexBetheAmplitude_adjacent_exchange hc p sigma i
  have hamp : sixVertexBetheAmplitude c p
      (sigma * Equiv.swap i.castSucc i.succ) =
      -Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
        sixVertexBetheAmplitude c p sigma := by
    have hcancel : Complex.exp (-Complex.I *
        sixVertexTheta c 0 (p (sigma a))) *
        Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a))) = 1 := by
      rw [← Complex.exp_add]
      ring_nf
      simp
    rw [hzero, hell] at hamp0
    change Complex.exp (-Complex.I * sixVertexTheta c (p (sigma a)) 0) *
        sixVertexBetheAmplitude c p
          (sigma * Equiv.swap i.castSucc i.succ) =
        -sixVertexBetheAmplitude c p sigma at hamp0
    rw [sixVertexTheta_antisymm c 0 (p (sigma a))] at hamp0
    have hamp0' : Complex.exp (Complex.I *
        sixVertexTheta c 0 (p (sigma a))) *
        sixVertexBetheAmplitude c p
          (sigma * Equiv.swap i.castSucc i.succ) =
        -sixVertexBetheAmplitude c p sigma := by
      convert hamp0 using 1
      push_cast
      ring
    calc
      _ = (Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
          Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a)))) *
          sixVertexBetheAmplitude c p
            (sigma * Equiv.swap i.castSucc i.succ) := by
              rw [hcancel, one_mul]
      _ = Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
          (Complex.exp (Complex.I * sixVertexTheta c 0 (p (sigma a))) *
            sixVertexBetheAmplitude c p
              (sigma * Equiv.swap i.castSucc i.succ)) := by ring
      _ = _ := by rw [hamp0']; ring
  have hrem := sixVertexBetheWordCoefficientRemainder_adjacent_invariant
    c z sigma w i hiM hiL
  have hmono := sixVertexBetheWordMonomial_adjacent_invariant
    (N := N) z sigma x w i hiM hiL
  unfold sixVertexBethePerturbedWordTerm
  change sixVertexBetheAmplitude c p sigma *
      sixVertexBetheWordCoefficient c z sigma w *
        sixVertexBetheWordMonomial N z sigma x w +
      sixVertexBetheAmplitude c p (sigma * Equiv.swap a b) *
        sixVertexBetheWordCoefficient c z (sigma * Equiv.swap a b) w *
          sixVertexBetheWordMonomial N z (sigma * Equiv.swap a b) x w = _
  rw [sixVertexBetheWordCoefficient_eq_ML_mul_remainder
      c z sigma w i hiM hiL,
    sixVertexBetheWordCoefficient_eq_ML_mul_remainder
      c z (sigma * Equiv.swap i.castSucc i.succ) w i hiM hiL]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  rw [hrem, hmono, hamp, hza, hzb]
  have hfactor := sixVertexBetheZeroAdjacentPairFactor_eq_deriv
    hc hphase heps
  calc
    _ = ((sixVertexBetheM c (sixVertexBethePhase (p (sigma a))) *
            sixVertexBetheL c (sixVertexBethePhase eps) - 1) -
          Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma a))) *
            (sixVertexBetheM c (sixVertexBethePhase eps) *
              sixVertexBetheL c (sixVertexBethePhase (p (sigma a))) - 1)) *
        sixVertexBetheAmplitude c p sigma *
        sixVertexBetheWordCoefficientRemainder c z sigma w i.castSucc *
        sixVertexBetheWordMonomial N z sigma x w := by ring
    _ = _ := by
      rw [hfactor]
      dsimp only [a, z]
      ring


theorem sixVertexBetheZeroBoundaryPairFactor_tendsto
    {c : Real} (hc : 2 < c) {N : Nat} {y : Real}
    (hy : sixVertexBethePhase y ≠ 1) :
    Tendsto (fun eps : Real =>
      (sixVertexBetheM c (sixVertexBethePhase y) *
          sixVertexBetheL c (sixVertexBethePhase eps) - 1) -
        Complex.exp (-Complex.I * sixVertexTheta c 0 y) *
          sixVertexBethePhase eps ^ N *
          (sixVertexBetheM c (sixVertexBethePhase eps) *
            sixVertexBetheL c (sixVertexBethePhase y) - 1))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 *
        sixVertexBetheM c (sixVertexBethePhase y) *
          (sixVertexThetaLeftDerivAtZero c y + N))) := by
  let E := Complex.exp (-Complex.I * sixVertexTheta c 0 y)
  let My := sixVertexBetheM c (sixVertexBethePhase y)
  let Ly := sixVertexBetheL c (sixVertexBethePhase y)
  have hordinary : Tendsto (fun _eps : Real =>
      (c : Complex) ^ 2 * My * sixVertexThetaLeftDerivAtZero c y)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * My *
        sixVertexThetaLeftDerivAtZero c y)) := tendsto_const_nhds
  have hvanish : Tendsto (fun eps : Real =>
      1 - sixVertexBethePhase eps ^ N)
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds (0 : Complex)) := by
    have hcont : Continuous (fun eps : Real =>
        (1 : Complex) - sixVertexBethePhase eps ^ N) := by
      unfold sixVertexBethePhase
      fun_prop
    have h := hcont.continuousAt.mono_left
      (inf_le_left : nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ ≤
        nhds (0 : Real))
    convert h using 1
    simp [sixVertexBethePhase]
  have hM := sixVertexBetheM_phase_mul_one_sub_pow_tendsto c N
  have hcorr : Tendsto (fun eps : Real => E *
      (1 - sixVertexBethePhase eps ^ N) *
        (sixVertexBetheM c (sixVertexBethePhase eps) * Ly - 1))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * N * My)) := by
    have hinner : Tendsto (fun eps : Real =>
        (1 - sixVertexBethePhase eps ^ N) *
          (sixVertexBetheM c (sixVertexBethePhase eps) * Ly - 1))
        (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
        (nhds (-((c : Complex) ^ 2 * N) * Ly)) := by
      have hLy : Tendsto (fun _eps : Real => Ly)
          (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
          (nhds Ly) := tendsto_const_nhds
      have hraw := (hM.mul hLy).sub hvanish
      convert hraw using 1
      · funext eps
        ring
      · ring
    have hEconst : Tendsto (fun _eps : Real => E)
        (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
        (nhds E) := tendsto_const_nhds
    have hraw := hEconst.mul hinner
    have hE := sixVertexTheta_zero_exp_neg_eq_neg_M_div_L hc hy
    have hL := sixVertexBetheL_phase_ne_zero hc y
    have hlimit : E * (-((c : Complex) ^ 2 * N) * Ly) =
        (c : Complex) ^ 2 * N * My := by
      dsimp only [E, My, Ly]
      rw [hE]
      field_simp [hL]
    convert hraw using 1
    · funext eps
      ring
    · rw [hlimit]
  have hsum := hordinary.add hcorr
  have hsum' : Tendsto (fun eps : Real =>
      (c : Complex) ^ 2 * My * sixVertexThetaLeftDerivAtZero c y +
        E * (1 - sixVertexBethePhase eps ^ N) *
          (sixVertexBetheM c (sixVertexBethePhase eps) * Ly - 1))
      (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ)
      (nhds ((c : Complex) ^ 2 * My *
        (sixVertexThetaLeftDerivAtZero c y + N))) := by
    convert hsum using 1 <;> ring
  apply hsum'.congr'
  have hne : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    simpa using heps
  have hinter : ∀ᶠ eps in nhdsWithin (0 : Real)
      (Set.singleton (0 : Real))ᶜ, eps ∈ Set.Ioo (-Real.pi) Real.pi :=
    mem_inf_of_left (Ioo_mem_nhds
      (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  filter_upwards [hne, hinter] with eps hneps heps
  have hphase := sixVertexBethePhase_ne_one_of_mem_Ioo_of_ne_zero
    heps hneps
  have hord := sixVertexBetheZeroAdjacentPairFactor_eq_deriv hc hy hphase
  dsimp only [E, My, Ly]
  rw [← hord]
  ring


theorem sum_sixVertexBethePerturbedWordTerm_adjacent_eq_zeroPairs
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 1) → Real) (ell : Fin (n + 1)) (eps : Real)
    (x : Fin (n + 1) → Int) (w : Finset (Fin (n + 1)))
    (i : Fin n) (hiM : i.castSucc ∉ w) (hiL : i.succ ∈ w)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 1)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) =
      ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell,
        (sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * Equiv.swap i.castSucc i.succ)) := by
  let a : Fin (n + 1) := i.castSucc
  let b : Fin (n + 1) := i.succ
  let T : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
    sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  have hsplit (sigma : Equiv.Perm (Fin (n + 1))) :
      T sigma =
        (if sigma a ≠ ell ∧ sigma b ≠ ell then T sigma else 0) +
        (if sigma a = ell then T sigma else 0) +
        (if sigma b = ell then T sigma else 0) := by
    by_cases ha : sigma a = ell
    · have hb : sigma b ≠ ell := by
        intro hb
        exact hab (sigma.injective (ha.trans hb.symm))
      simp [ha, hb]
    · by_cases hb : sigma b = ell
      · simp [ha, hb]
      · simp [ha, hb]
  have haway : (∑ sigma : Equiv.Perm (Fin (n + 1)) with
      sigma a ≠ ell ∧ sigma b ≠ ell, T sigma) = 0 := by
    simpa [T, a, b] using
      sum_sixVertexBethePerturbedWordTerm_adjacent_away_zero_eq_zero
        hc p ell eps x w i hiM hiL hother
  have hreindex :
      (∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma a = ell, T sigma) =
      ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma b = ell,
        T (sigma * Equiv.swap a b) := by
    let tau := Equiv.swap a b
    let F : Equiv.Perm (Fin (n + 1)) → Complex := fun sigma =>
      if sigma a = ell then T sigma else 0
    have hsum := (Equiv.sum_comp (Equiv.mulRight tau) F).symm
    rw [Finset.sum_filter, Finset.sum_filter]
    change (∑ sigma, if sigma a = ell then T sigma else 0) = _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    simp [F, tau, Equiv.Perm.mul_apply, a, b]
  calc
    (∑ sigma, T sigma) = ∑ sigma,
        ((if sigma a ≠ ell ∧ sigma b ≠ ell then T sigma else 0) +
        (if sigma a = ell then T sigma else 0) +
        (if sigma b = ell then T sigma else 0)) := by
          apply Finset.sum_congr rfl
          intro sigma hsigma
          exact hsplit sigma
    _ = (∑ sigma with sigma a ≠ ell ∧ sigma b ≠ ell, T sigma) +
        (∑ sigma with sigma a = ell, T sigma) +
        (∑ sigma with sigma b = ell, T sigma) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    _ = (∑ sigma with sigma a = ell, T sigma) +
        (∑ sigma with sigma b = ell, T sigma) := by rw [haway, zero_add]
    _ = (∑ sigma with sigma b = ell, T (sigma * Equiv.swap a b)) +
        (∑ sigma with sigma b = ell, T sigma) := by rw [hreindex]
    _ = ∑ sigma with sigma b = ell,
        (T sigma + T (sigma * Equiv.swap a b)) := by
          rw [Finset.sum_add_distrib, add_comm]
    _ = _ := by rfl

theorem sum_sixVertexBethePerturbedWordTerm_boundary_eq_zeroPairs
    {c : Real} (hc : 2 < c) {N n : Nat}
    (p : Fin (n + 2) → Real)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
    (ell : Fin (n + 2)) (eps : Real) (x : Fin (n + 2) → Int)
    (w : Finset (Fin (n + 2)))
    (hlastM : Fin.last (n + 1) ∉ w) (hzeroL : (0 : Fin (n + 2)) ∈ w)
    (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
    (∑ sigma : Equiv.Perm (Fin (n + 2)),
      sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) =
      ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell,
        (sixVertexBethePerturbedWordTerm N c p ell eps x w sigma +
          sixVertexBethePerturbedWordTerm N c p ell eps x w
            (sigma * Equiv.swap (Fin.last (n + 1)) 0)) := by
  let a : Fin (n + 2) := Fin.last (n + 1)
  let b : Fin (n + 2) := 0
  let T : Equiv.Perm (Fin (n + 2)) → Complex := fun sigma =>
    sixVertexBethePerturbedWordTerm N c p ell eps x w sigma
  have hab : a ≠ b := by simp [a, b]
  have hsplit (sigma : Equiv.Perm (Fin (n + 2))) :
      T sigma =
        (if sigma a ≠ ell ∧ sigma b ≠ ell then T sigma else 0) +
        (if sigma a = ell then T sigma else 0) +
        (if sigma b = ell then T sigma else 0) := by
    by_cases ha : sigma a = ell
    · have hb : sigma b ≠ ell := by
        intro hb
        exact hab (sigma.injective (ha.trans hb.symm))
      simp [ha, hb]
    · by_cases hb : sigma b = ell
      · simp [ha, hb]
      · simp [ha, hb]
  have haway : (∑ sigma : Equiv.Perm (Fin (n + 2)) with
      sigma a ≠ ell ∧ sigma b ≠ ell, T sigma) = 0 := by
    simpa [T, a, b] using
      sum_sixVertexBethePerturbedWordTerm_boundary_away_zero_eq_zero
        hc p hp ell eps x w hlastM hzeroL hother
  have hreindex :
      (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma a = ell, T sigma) =
      ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma b = ell,
        T (sigma * Equiv.swap a b) := by
    let tau := Equiv.swap a b
    let F : Equiv.Perm (Fin (n + 2)) → Complex := fun sigma =>
      if sigma a = ell then T sigma else 0
    have hsum := (Equiv.sum_comp (Equiv.mulRight tau) F).symm
    rw [Finset.sum_filter, Finset.sum_filter]
    change (∑ sigma, if sigma a = ell then T sigma else 0) = _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    simp [F, tau, Equiv.Perm.mul_apply, a, b]
  calc
    (∑ sigma, T sigma) = ∑ sigma,
        ((if sigma a ≠ ell ∧ sigma b ≠ ell then T sigma else 0) +
        (if sigma a = ell then T sigma else 0) +
        (if sigma b = ell then T sigma else 0)) := by
          apply Finset.sum_congr rfl
          intro sigma hsigma
          exact hsplit sigma
    _ = (∑ sigma with sigma a ≠ ell ∧ sigma b ≠ ell, T sigma) +
        (∑ sigma with sigma a = ell, T sigma) +
        (∑ sigma with sigma b = ell, T sigma) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    _ = (∑ sigma with sigma a = ell, T sigma) +
        (∑ sigma with sigma b = ell, T sigma) := by rw [haway, zero_add]
    _ = (∑ sigma with sigma b = ell, T (sigma * Equiv.swap a b)) +
        (∑ sigma with sigma b = ell, T sigma) := by rw [hreindex]
    _ = ∑ sigma with sigma b = ell,
        (T sigma + T (sigma * Equiv.swap a b)) := by
          rw [Finset.sum_add_distrib, add_comm]
    _ = _ := by rfl


theorem sixVertexBetheWordCoefficientRemainder_perturb_eq
    {n : Nat} (c : Real) (p : Fin (n + 1) → Real)
    (ell : Fin (n + 1)) (eps : Real)
    (w : Finset (Fin (n + 1))) (a : Fin (n + 1))
    (hML : sixVertexBetheMLBoundarySet w = {a})
    (sigma : Equiv.Perm (Fin (n + 1)))
    (hzero : sigma (finRotate (n + 1) a) = ell) :
    sixVertexBetheWordCoefficientRemainder c
        (fun j => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps j)) sigma w a =
      sixVertexBetheWordCoefficientRemainder c
        (fun j => sixVertexBethePhase (p j)) sigma w a := by
  let b := finRotate (n + 1) a
  have haBound : a ∈ sixVertexBetheMLBoundarySet w := by simp [hML]
  have haML := (mem_sixVertexBetheMLBoundarySet w a).mp haBound
  unfold sixVertexBetheWordCoefficientRemainder
  apply Finset.prod_congr rfl
  intro k hk
  have hka : k ≠ a := (Finset.mem_erase.mp hk).1
  unfold sixVertexBetheWordEdgeFactor
  by_cases hkw : k ∈ w
  · by_cases hrw : finRotate (n + 1) k ∈ w
    · simp only [hkw, hrw, if_true]
      have hroot : sigma (finRotate (n + 1) k) ≠ ell := by
        intro h
        have heq : finRotate (n + 1) k = b :=
          sigma.injective (h.trans hzero.symm)
        apply hka
        exact (finRotate (n + 1)).injective heq
      rw [sixVertexBethePerturbRoot_ne p ell _ hroot]
    · have hrw' : k + 1 ∉ w := by
        simpa [finRotate_apply] using hrw
      simp [hkw, hrw']
  · by_cases hrw : finRotate (n + 1) k ∈ w
    · have hkBound : k ∈ sixVertexBetheMLBoundarySet w :=
        (mem_sixVertexBetheMLBoundarySet w k).2 ⟨hkw, hrw⟩
      have hkeq : k = a := by simpa [hML] using hkBound
      exact (hka hkeq).elim
    · simp only [hkw, hrw, if_false]
      have hroot : sigma k ≠ ell := by
        intro h
        have hkb : k = b := sigma.injective (h.trans hzero.symm)
        exact hkw (hkb.symm ▸ haML.2)
      rw [sixVertexBethePerturbRoot_ne p ell _ hroot]

theorem continuous_sixVertexBethePerturbedWordMonomial
    {n N : Nat} (p : Fin (n + 1) → Real) (ell : Fin (n + 1))
    (sigma : Equiv.Perm (Fin (n + 1))) (x : Fin (n + 1) → Int)
    (w : Finset (Fin (n + 1))) :
    Continuous (fun eps : Real =>
      sixVertexBetheWordMonomial N
        (fun j => sixVertexBethePhase
          (sixVertexBethePerturbRoot p ell eps j)) sigma x w) := by
  let e : Fin (n + 1) → Int := fun i =>
    if i ∈ w then sixVertexBetheShiftCoordinates N x i else x i
  have h := continuous_sixVertexBethePerturbedIntMonomial p ell sigma e
  convert h using 1
  funext eps
  unfold sixVertexBetheWordMonomial sixVertexBetheIntMonomial
  apply Finset.prod_congr rfl
  intro i hi
  simp [e]

end
end StatMech.FrontierD
