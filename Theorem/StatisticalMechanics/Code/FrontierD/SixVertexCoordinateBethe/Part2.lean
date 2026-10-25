/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Mathlib.GroupTheory.Perm.Fin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBethePairFactor_phase (c p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase p)
        (sixVertexBethePhase q) =
      sixVertexBethePhase p *
        (sixVertexBethePhase (-p) + sixVertexBethePhase q -
          2 * sixVertexDelta c) := by
  have hunit : sixVertexBethePhase p * sixVertexBethePhase (-p) = 1 := by
    rw [sixVertexBethePhase_neg]
    calc
      sixVertexBethePhase p * star (sixVertexBethePhase p) =
          (Complex.normSq (sixVertexBethePhase p) : ℂ) :=
        Complex.mul_conj (sixVertexBethePhase p)
      _ = (‖sixVertexBethePhase p‖ ^ 2 : ℝ) := by
        rw [Complex.normSq_eq_norm_sq]
      _ = 1 := by rw [sixVertexBethePhase_norm]; norm_num
  unfold sixVertexBethePairFactor
  rw [← hunit]
  ring

theorem sixVertexScatteringDenominator_eq_phase (c p q : ℝ) :
    sixVertexScatteringDenominator c p q =
      sixVertexBethePhase p + sixVertexBethePhase (-q) -
        2 * sixVertexDelta c := by
  unfold sixVertexScatteringDenominator sixVertexBethePhase
  congr 2
  push_cast
  ring_nf

theorem sixVertexBethePairFactor_eq_phase_mul_conj_denominator
    (c p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase p)
        (sixVertexBethePhase q) =
      sixVertexBethePhase p *
        star (sixVertexScatteringDenominator c p q) := by
  rw [sixVertexBethePairFactor_phase,
    sixVertexScatteringDenominator_eq_phase]
  congr 1
  apply Complex.ext <;> simp [sixVertexBethePhase_neg]

theorem sixVertexBethePairFactor_swap_eq_phase_mul_denominator
    (c p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase q)
        (sixVertexBethePhase p) =
      sixVertexBethePhase q * sixVertexScatteringDenominator c p q := by
  rw [sixVertexBethePairFactor_phase,
    sixVertexScatteringDenominator_eq_phase]
  ring

theorem sixVertexBethePairFactor_phase_ne_zero {c : ℝ} (hc : 2 < c)
    (p q : ℝ) :
    sixVertexBethePairFactor c (sixVertexBethePhase p)
      (sixVertexBethePhase q) ≠ 0 := by
  rw [sixVertexBethePairFactor_eq_phase_mul_conj_denominator]
  exact mul_ne_zero (Complex.exp_ne_zero _)
    (star_ne_zero.mpr (sixVertexScatteringDenominator_ne_zero hc p q))

theorem sixVertexBethePhase_sub_mul (p q : ℝ) :
    Complex.exp (Complex.I * (p - q)) * sixVertexBethePhase q =
      sixVertexBethePhase p := by
  unfold sixVertexBethePhase
  rw [← Complex.exp_add]
  congr 1
  ring_nf

theorem sixVertexBethePhase_injective_on_Ioo :
    Set.InjOn sixVertexBethePhase (Set.Ioo (-Real.pi) Real.pi) := by
  intro p hp q hq heq
  rw [sixVertexBethePhase, sixVertexBethePhase] at heq
  rcases Complex.exp_eq_exp_iff_exists_int.mp heq with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  norm_num at him
  have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmlo : (-1 : ℝ) < (m : ℝ) := by
    by_contra h
    have hmle : (m : ℝ) ≤ -1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hmle htwopi.le
    nlinarith [hp.1, hq.2, Real.pi_pos]
  have hmhi : (m : ℝ) < 1 := by
    by_contra h
    have hmge : (1 : ℝ) ≤ m := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hmge htwopi.le
    nlinarith [hp.2, hq.1, Real.pi_pos]
  have hmlo' : (-1 : ℤ) < m := by exact_mod_cast hmlo
  have hmhi' : m < (1 : ℤ) := by exact_mod_cast hmhi
  have hm0 : m = 0 := by omega
  subst m
  norm_num at him
  exact him

theorem SixVertexOpenRootSimplex.phase_injective
    {n : ℕ} {p : Fin n → ℝ} (hp : SixVertexOpenRootSimplex p) :
    Function.Injective fun j => sixVertexBethePhase (p j) := by
  intro j k hjk
  apply hp.1.injective
  exact sixVertexBethePhase_injective_on_Ioo (hp.2.2 j) (hp.2.2 k) hjk

theorem SixVertexOpenRootSimplex.ne_zero_of_even
    {k : ℕ} {p : Fin (k + k) → ℝ} (hp : SixVertexOpenRootSimplex p)
    (j : Fin (k + k)) : p j ≠ 0 := by
  intro hjzero
  have hrevzero : p j.rev = 0 := by rw [hp.2.1, hjzero, neg_zero]
  have hjrev : j.rev = j := hp.1.injective (hrevzero.trans hjzero.symm)
  have hval := congrArg Fin.val hjrev
  simp only [Fin.rev, Fin.val_mk] at hval
  omega

theorem SixVertexOpenRootSimplex.phase_ne_one_of_even
    {k : ℕ} {p : Fin (k + k) → ℝ} (hp : SixVertexOpenRootSimplex p)
    (j : Fin (k + k)) : sixVertexBethePhase (p j) ≠ 1 := by
  intro hphase
  have hphase0 : sixVertexBethePhase (p j) = sixVertexBethePhase 0 := by
    simpa [sixVertexBethePhase] using hphase
  have hpzero := sixVertexBethePhase_injective_on_Ioo (hp.2.2 j)
    ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩ hphase0
  exact hp.ne_zero_of_even j hpzero


theorem sixVertexBethePairFactor_exchange {c : ℝ} (hc : 2 < c)
    (p q : ℝ) :
    Complex.exp (-Complex.I * sixVertexTheta c p q) *
        sixVertexBethePairFactor c (sixVertexBethePhase q)
          (sixVertexBethePhase p) =
      sixVertexBethePairFactor c (sixVertexBethePhase p)
        (sixVertexBethePhase q) := by
  rw [sixVertexTheta_exp_identity hc,
    sixVertexBethePairFactor_swap_eq_phase_mul_denominator,
    sixVertexBethePairFactor_eq_phase_mul_conj_denominator]
  field_simp [sixVertexScatteringDenominator_ne_zero hc p q]
  rw [sixVertexBethePhase_sub_mul]

theorem sixVertexBethePhase_pow (N : ℕ) (p : ℝ) :
    sixVertexBethePhase p ^ N =
      Complex.exp (Complex.I * ((N : ℝ) * p)) := by
  rw [sixVertexBethePhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf


theorem SixVertexSatisfiesMultiplicativeBetheEquations.pairFactor_periodic
    {c : ℝ} (hc : 2 < c) {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
    (j : Fin n) :
    sixVertexBethePhase (p j) ^ N *
        (∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
          (sixVertexBethePhase (p j))) =
      (-1 : ℂ) ^ (n - 1) *
        ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p j))
          (sixVertexBethePhase (p k)) := by
  have hsum :
      -Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ) =
        ∑ k, -Complex.I * sixVertexTheta c (p j) (p k) := by
    push_cast
    rw [Finset.mul_sum]
  have hexchange :
      Complex.exp (-Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ)) *
          (∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
            (sixVertexBethePhase (p j))) =
        ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p j))
          (sixVertexBethePhase (p k)) := by
    rw [hsum, Complex.exp_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    exact sixVertexBethePairFactor_exchange hc (p j) (p k)
  rw [sixVertexBethePhase_pow, hp j]
  calc
    ((-1 : ℂ) ^ (n - 1) *
        Complex.exp (-Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ))) *
          ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
            (sixVertexBethePhase (p j)) =
      (-1 : ℂ) ^ (n - 1) *
        (Complex.exp (-Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ)) *
          ∏ k, sixVertexBethePairFactor c (sixVertexBethePhase (p k))
            (sixVertexBethePhase (p j))) := by ring
    _ = _ := by rw [hexchange]


end
end StatMech.FrontierD
