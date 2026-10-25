/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheScattering.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEquations.Part7
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem exp_two_pi_mul_centralQuantumNumber {n : ℕ} (j : Fin n) :
    Complex.exp (Complex.I *
      (2 * Real.pi * sixVertexCentralQuantumNumber j)) =
        (-1 : ℂ) ^ (n - 1) := by
  have hquantum :
      2 * Real.pi * sixVertexCentralQuantumNumber j =
        2 * Real.pi * (j.val : ℝ) - (n - 1 : ℕ) * Real.pi := by
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      exact Fin.elim0 j
    have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    rw [Nat.cast_sub hn]
    simp [sixVertexCentralQuantumNumber]
    ring
  have hquantumc :
      (2 : ℂ) * (Real.pi : ℂ) *
          (sixVertexCentralQuantumNumber j : ℂ) =
        (2 : ℂ) * (Real.pi : ℂ) * (j.val : ℂ) -
          (((n - 1 : ℕ) : ℝ) : ℂ) * (Real.pi : ℂ) := by
    have hc := congrArg (fun z : ℝ => (z : ℂ)) hquantum
    push_cast at hc
    exact hc
  rw [hquantumc]
  have hsplit :
      Complex.I *
          ((2 : ℂ) * (Real.pi : ℂ) * (j.val : ℂ) -
            (((n - 1 : ℕ) : ℝ) : ℂ) * (Real.pi : ℂ)) =
        ((j.val : ℂ) * (2 * Real.pi * Complex.I)) +
          (((-((n - 1 : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  rw [Complex.exp_nat_mul_two_pi_mul_I]
  simp only [one_mul]
  rw [Complex.exp_ofReal_mul_I,
    show -((n - 1 : ℕ) : ℝ) * Real.pi =
      -(((n - 1 : ℕ) : ℝ) * Real.pi) by ring,
    Real.cos_neg, Real.sin_neg,
    Real.cos_nat_mul_pi, Real.sin_nat_mul_pi]
  norm_num


theorem SixVertexSatisfiesBetheEquations.multiplicative
    {c : ℝ} {N n : ℕ} {p : Fin n → ℝ}
    (hp : SixVertexSatisfiesBetheEquations c N n p) :
    SixVertexSatisfiesMultiplicativeBetheEquations c N n p := by
  intro j
  have hj := hp j
  have harg :
      Complex.I * (((N : ℝ) : ℂ) * (p j : ℂ)) =
        Complex.I * ((2 : ℂ) * (Real.pi : ℂ) *
            (sixVertexCentralQuantumNumber j : ℂ)) +
          (-Complex.I *
            ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ)) := by
    calc
      _ = Complex.I * (((N : ℝ) * p j : ℝ) : ℂ) := by
        push_cast
        ring
      _ = Complex.I *
          ((2 * Real.pi * sixVertexCentralQuantumNumber j -
            ∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ) := by
              congr 1
              exact_mod_cast hj
      _ = _ := by
        push_cast
        ring
  rw [harg, Complex.exp_add, exp_two_pi_mul_centralQuantumNumber]

theorem exp_neg_I_sum_sixVertexTheta_eq_product
    {c : ℝ} (hc : 2 < c) {n : ℕ} (p : Fin n → ℝ) (j : Fin n) :
    Complex.exp (-Complex.I * ∑ k, sixVertexTheta c (p j) (p k)) =
      ∏ k, Complex.exp (Complex.I * (p j - p k)) *
        star (sixVertexScatteringDenominator c (p j) (p k)) /
          sixVertexScatteringDenominator c (p j) (p k) := by
  have hsum :
      -Complex.I *
          ((∑ k, sixVertexTheta c (p j) (p k) : ℝ) : ℂ) =
        ∑ k, -Complex.I * sixVertexTheta c (p j) (p k) := by
    push_cast
    rw [Finset.mul_sum]
  rw [hsum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro k _
  exact sixVertexTheta_exp_identity hc (p j) (p k)

end
end StatMech.FrontierD
