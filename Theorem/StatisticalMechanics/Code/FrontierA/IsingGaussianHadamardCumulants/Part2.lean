/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants.Part2
open Filter
open scoped BigOperators Complex Nat


namespace StatMech.FrontierA

noncomputable section

theorem normalizedIteratedDeriv_logDeriv_recurrence
    (F : Complex -> Complex) (hF : AnalyticAt Complex F 0)
    (hF0 : F 0 ≠ 0) (order : Nat) :
    iteratedDeriv (order + 1) F 0 / F 0 =
      ∑ k ∈ Finset.range (order + 1),
        (order.choose k : Complex) *
          iteratedDeriv k (logDeriv F) 0 *
            (iteratedDeriv (order - k) F 0 / F 0) := by
  have hlog : AnalyticAt Complex (logDeriv F) 0 := by
    change AnalyticAt Complex (fun z => deriv F z / F z) 0
    exact hF.deriv.div hF hF0
  have hnonzero : Filter.Eventually (fun z : Complex => F z ≠ 0)
      (nhds (0 : Complex)) :=
    hF.continuousAt.eventually_ne hF0
  have hidentity : Filter.EventuallyEq (nhds (0 : Complex))
      (deriv F) (fun z => logDeriv F z * F z) := by
    filter_upwards [hnonzero] with z hz
    rw [logDeriv_apply, div_mul_cancel₀ _ hz]
  have hderivative := hidentity.iteratedDeriv_eq order
  change iteratedDeriv order (deriv F) 0 =
    iteratedDeriv order (fun z => logDeriv F z * F z) 0 at hderivative
  rw [← iteratedDeriv_succ'] at hderivative
  have hproduct :
      iteratedDeriv order (fun z => logDeriv F z * F z) 0 =
        ∑ k ∈ Finset.range (order + 1),
          (order.choose k : Complex) *
            iteratedDeriv k (logDeriv F) 0 *
              iteratedDeriv (order - k) F 0 := by
    simpa only [Pi.mul_apply] using
      (iteratedDeriv_mul (n := order) (x := (0 : Complex))
        hlog.contDiffAt hF.contDiffAt)
  rw [hproduct] at hderivative
  calc
    iteratedDeriv (order + 1) F 0 / F 0 =
        (∑ k ∈ Finset.range (order + 1),
          (order.choose k : Complex) *
            iteratedDeriv k (logDeriv F) 0 *
              iteratedDeriv (order - k) F 0) / F 0 := by
      rw [hderivative]
    _ = _ := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem EvenHadamardFactorization.hadamardScalarCumulant_even
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (m : Nat) (hm : 1 ≤ m) :
    hadamardScalarCumulant F (2 * m) =
      -2 * (-1 : Real) ^ m * (Nat.factorial (2 * m - 1) : Real) *
        (∑' n, hF.roots n ^ m) := by
  unfold hadamardScalarCumulant
  rw [if_neg (by omega)]
  have hc := hF.iteratedDeriv_logDeriv_odd m hm
  have hcast :
      -2 * (-1 : Complex) ^ m *
          (Nat.factorial (2 * m - 1) : Complex) *
            (∑' n, hF.roots n ^ m) =
        ((-2 * (-1 : Real) ^ m *
          (Nat.factorial (2 * m - 1) : Real) *
            (∑' n, hF.roots n ^ m) : Real) : Complex) := by
    push_cast
    rfl
  rw [hcast] at hc
  exact congrArg Complex.re hc

@[simp] theorem hadamardScalarCumulant_zero (F : Complex → Complex) :
    hadamardScalarCumulant F 0 = 0 := by
  simp [hadamardScalarCumulant]

theorem EvenHadamardFactorization.hadamardScalarCumulant_odd
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) (horder : Odd order) :
    hadamardScalarCumulant F order = 0 := by
  obtain ⟨m, rfl⟩ := horder
  unfold hadamardScalarCumulant
  rw [if_neg (by omega)]
  have heven : Even (2 * m + 1 - 1) := by
    use m
    omega
  rw [hF.iteratedDeriv_logDeriv_even _ heven]
  rfl


theorem EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant
    {F : Complex -> Complex} (hF : EvenHadamardFactorization F)
    (order : Nat) :
    iteratedDeriv order (logDeriv F) 0 =
      (hadamardScalarCumulant F (order + 1) : Complex) := by
  unfold hadamardScalarCumulant
  rw [if_neg (by omega), Nat.add_sub_cancel]
  rcases Nat.even_or_odd order with horder | horder
  · rw [hF.iteratedDeriv_logDeriv_even order horder]
    rfl
  · obtain ⟨m, hm⟩ := horder
    have hindex : order = 2 * (m + 1) - 1 := by omega
    have hformula := hF.iteratedDeriv_logDeriv_odd (m + 1) (by omega)
    rw [← hindex] at hformula
    have hcast :
        -2 * (-1 : Complex) ^ (m + 1) *
            (Nat.factorial order : Complex) *
              (∑' n, hF.roots n ^ (m + 1)) =
          ((-2 * (-1 : Real) ^ (m + 1) *
            (Nat.factorial order : Real) *
              (∑' n, hF.roots n ^ (m + 1)) : Real) : Complex) := by
      push_cast
      rfl
    have hcomplex := hformula.trans hcast
    have hreal := congrArg Complex.re hcomplex
    calc
      iteratedDeriv order (logDeriv F) 0 =
          ((-2 * (-1 : Real) ^ (m + 1) *
            (Nat.factorial order : Real) *
              (∑' n, hF.roots n ^ (m + 1)) : Real) : Complex) := hcomplex
      _ = ((iteratedDeriv order (logDeriv F) 0).re : Complex) := by
        rw [hreal]
        simp only [Complex.ofReal_re]

theorem EvenHadamardFactorization.hadamardScalarCumulant_two
    {F : Complex → Complex} (hF : EvenHadamardFactorization F) :
    hadamardScalarCumulant F 2 = 2 * ∑' n, hF.roots n := by
  convert hF.hadamardScalarCumulant_even 1 (by omega) using 1 <;>
    norm_num

theorem EvenHadamardFactorization.hadamardScalarCumulant_four
    {F : Complex → Complex} (hF : EvenHadamardFactorization F) :
    hadamardScalarCumulant F 4 = -12 * ∑' n, hF.roots n ^ 2 := by
  convert hF.hadamardScalarCumulant_even 2 (by omega) using 1 <;>
    norm_num

theorem EvenHadamardFactorization.abs_hadamardScalarCumulant_even
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    (m : Nat) (hm : 1 ≤ m) :
    |hadamardScalarCumulant F (2 * m)| =
      2 * (Nat.factorial (2 * m - 1) : Real) *
        (∑' n, hF.roots n ^ m) := by
  rw [hF.hadamardScalarCumulant_even m hm]
  have hsum : 0 ≤ ∑' n, hF.roots n ^ m :=
    tsum_nonneg fun n => pow_nonneg (hF.roots_nonneg n) m
  rw [abs_mul, abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
    abs_neg_one_pow,
    abs_of_nonneg (Nat.cast_nonneg (Nat.factorial (2 * m - 1))),
    abs_of_nonneg hsum]
  ring

theorem two_factorial_pred_le_factorial
    (m : Nat) (hm : 1 ≤ m) :
    2 * (Nat.factorial (2 * m - 1) : Real) ≤
      (Nat.factorial (2 * m) : Real) := by
  have hsucc : 2 * m - 1 + 1 = 2 * m := by omega
  have hfactorial : Nat.factorial (2 * m) =
      (2 * m) * Nat.factorial (2 * m - 1) := by
    rw [← hsucc, Nat.factorial_succ, hsucc]
  rw [hfactorial]
  push_cast
  have hfac : 0 ≤ (Nat.factorial (2 * m - 1) : Real) := by positivity
  have hmReal : (1 : Real) ≤ m := by exact_mod_cast hm
  nlinarith


end
end StatMech.FrontierA
