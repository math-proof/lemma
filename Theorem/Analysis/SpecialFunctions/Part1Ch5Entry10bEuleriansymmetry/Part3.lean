/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Def.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry.Part3
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry10bEuleriansymmetry

open scoped BigOperators

open Finset

noncomputable section

theorem berB_coeff (n : ℕ) :
    PowerSeries.coeff n berB = bernoulli n / (n.factorial : ℚ) := by
  simp [berB, bernoulliPowerSeries]

theorem berB2_rel :
    berB2 * ((PowerSeries.exp ℚ) ^ 2 - 1) = 2 * PowerSeries.X := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h2 : (PowerSeries.rescale (2 : ℚ))
        (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) =
      (PowerSeries.rescale (2 : ℚ)) PowerSeries.X := by rw [hB]
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h2
  rw [C2_eq] at h2
  have ha2 := exp_sq2
  rw [← ha2] at h2
  unfold berB2 berB
  exact h2

theorem berB4_rel :
    berB4 * ((PowerSeries.exp ℚ) ^ 4 - 1) = 4 * PowerSeries.X := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h4 : (PowerSeries.rescale (4 : ℚ))
        (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) =
      (PowerSeries.rescale (4 : ℚ)) PowerSeries.X := by rw [hB]
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h4
  rw [C4_eq] at h4
  have ha4 := exp_four
  rw [← ha4] at h4
  unfold berB4 berB
  exact h4

theorem exp_coeff_one : PowerSeries.coeff 1 (PowerSeries.exp ℚ) = 1 := by
  rw [PowerSeries.coeff_exp]; simp

theorem A2_ne : (PowerSeries.exp ℚ) ^ 2 - 1 ≠ 0 := by
  intro hz
  have hc := congrArg (PowerSeries.coeff 1) hz
  simp only [map_sub, map_zero, PowerSeries.coeff_one] at hc
  rw [exp_sq2, PowerSeries.coeff_rescale, exp_coeff_one] at hc
  norm_num at hc

theorem A4_ne : (PowerSeries.exp ℚ) ^ 4 - 1 ≠ 0 := by
  intro hz
  have hc := congrArg (PowerSeries.coeff 1) hz
  simp only [map_sub, map_zero, PowerSeries.coeff_one] at hc
  rw [exp_four, PowerSeries.coeff_rescale, exp_coeff_one] at hc
  norm_num at hc

theorem M_ne : ((PowerSeries.exp ℚ) ^ 2 - 1) * ((PowerSeries.exp ℚ) ^ 4 - 1) ≠ 0 :=
  mul_ne_zero A2_ne A4_ne

theorem hCinv : PowerSeries.C (2⁻¹ : ℚ) * (2 : PowerSeries ℚ) = 1 := by
  rw [← C2_eq, ← map_mul]
  have h12 : (2⁻¹ : ℚ) * 2 = 1 := by ring
  rw [h12, map_one]

theorem hEf : eulerEGF *
    (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) = 2 := by
  have hcosh : eulerEGF * coshPS = 1 := euler_cosh
  unfold coshPS at hcosh
  have hEC : (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
      PowerSeries.C (2⁻¹ : ℚ) = 1 := by
    calc (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
            PowerSeries.C (2⁻¹ : ℚ)
        = eulerEGF * ((PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
            PowerSeries.C (2⁻¹ : ℚ)) := by ring
      _ = 1 := hcosh
  calc eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))
      = (eulerEGF * (PowerSeries.exp ℚ +
          (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) * 1 := by ring
    _ = (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
          (PowerSeries.C (2⁻¹ : ℚ) * 2) := by rw [← hCinv]
    _ = ((eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
          PowerSeries.C (2⁻¹ : ℚ)) * 2 := by ring
    _ = 2 := by rw [hEC]; ring

theorem hTf :
    (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
    2 * tanhPS := by
  unfold tanhPS sinhPS
  calc (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF
      = ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          eulerEGF) * 1 := by ring
    _ = ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF) *
          (PowerSeries.C (2⁻¹ : ℚ) * 2) := by rw [← hCinv]
    _ = 2 * (((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          PowerSeries.C (2⁻¹ : ℚ)) * eulerEGF) := by ring

theorem two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
  intro hz
  rw [← C2_eq] at hz
  have hc := congrArg (PowerSeries.coeff 0) hz
  simp only [PowerSeries.coeff_C, map_zero] at hc
  simp at hc

theorem G'_eq :
    (PowerSeries.X + berB4 - berB2) *
        (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) -
      PowerSeries.X * (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) = 0 := by
  have hR1 : berB4 * ((PowerSeries.exp ℚ) ^ 4 - 1) - 4 * PowerSeries.X = 0 := by
    rw [berB4_rel]; ring
  have hR2 : berB2 * ((PowerSeries.exp ℚ) ^ 2 - 1) - 2 * PowerSeries.X = 0 := by
    rw [berB2_rel]; ring
  have hR5 : PowerSeries.exp ℚ * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ) - 1 = 0 := by
    rw [exp_neg_mul]; ring
  have hcof := cofactor2 berB4 berB2 (PowerSeries.exp ℚ)
    ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) PowerSeries.X
  simp only at hcof
  rw [hR1, hR2, hR5] at hcof
  simp only [mul_zero, sub_zero, add_zero] at hcof
  have hM := M_ne
  have hGM : ((PowerSeries.X + berB4 - berB2) *
      (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) -
      PowerSeries.X * (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) *
      (((PowerSeries.exp ℚ) ^ 2 - 1) * ((PowerSeries.exp ℚ) ^ 4 - 1)) = 0 := hcof
  rcases mul_eq_zero.mp hGM with h | h
  · exact h
  · exact absurd h hM

theorem bernoulli_tanh :
    PowerSeries.X * tanhPS = PowerSeries.X + berB4 - berB2 := by
  have hG := G'_eq
  have hE := congrArg (· * eulerEGF) hG
  rw [sub_mul, zero_mul] at hE
  have e1 : (PowerSeries.X + berB4 - berB2) *
        (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
      (PowerSeries.X + berB4 - berB2) * 2 := by
    have hrw : (PowerSeries.X + berB4 - berB2) *
          (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
        (PowerSeries.X + berB4 - berB2) *
          (eulerEGF * (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ))) := by
      ring
    rw [hrw, hEf]
  have e2 : PowerSeries.X *
        (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
      PowerSeries.X * (2 * tanhPS) := by
    have hrw : PowerSeries.X *
          (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF =
        PowerSeries.X *
          ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) * eulerEGF) := by
      ring
    rw [hrw, hTf]
  rw [e1, e2] at hE
  have h3 : (2 : PowerSeries ℚ) *
      ((PowerSeries.X + berB4 - berB2) - PowerSeries.X * tanhPS) = 0 := by
    linear_combination hE
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd h two_ne
  · have heq : PowerSeries.X + berB4 - berB2 = PowerSeries.X * tanhPS :=
      sub_eq_zero.mp h
    rw [heq]

-- Derivatives
theorem derivative_rescale_q (a : ℚ) (f : PowerSeries ℚ) :
    PowerSeries.derivative ((PowerSeries.rescale a) f) =
      PowerSeries.C a * (PowerSeries.rescale a) (PowerSeries.derivative f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  ring

theorem derivative_neg_exp :
    PowerSeries.derivative ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      PowerSeries.C (-1) * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ) := by
  rw [derivative_rescale_q, PowerSeries.derivative_exp ℚ]

theorem derivative_sinh : PowerSeries.derivative sinhPS = coshPS := by
  unfold sinhPS coshPS
  have hde : PowerSeries.derivative (PowerSeries.exp ℚ) = PowerSeries.exp ℚ :=
    PowerSeries.derivative_exp ℚ
  have hCm1 : PowerSeries.C (-1 : ℚ) = -1 := by simp
  have e1 : PowerSeries.derivative
        ((PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          PowerSeries.C (2⁻¹ : ℚ)) =
      PowerSeries.C (2⁻¹ : ℚ) *
        (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) := by
    rw [Derivation.leibniz]
    simp only [PowerSeries.derivative_C, smul_eq_mul]
    rw [map_sub, hde, derivative_neg_exp, hCm1]
    ring
  rw [e1]
  ring

theorem derivative_cosh : PowerSeries.derivative coshPS = sinhPS := by
  unfold sinhPS coshPS
  have hde : PowerSeries.derivative (PowerSeries.exp ℚ) = PowerSeries.exp ℚ :=
    PowerSeries.derivative_exp ℚ
  have hCm1 : PowerSeries.C (-1 : ℚ) = -1 := by simp
  have e1 : PowerSeries.derivative
        ((PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
          PowerSeries.C (2⁻¹ : ℚ)) =
      PowerSeries.C (2⁻¹ : ℚ) *
        (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) := by
    rw [Derivation.leibniz]
    simp only [PowerSeries.derivative_C, smul_eq_mul]
    rw [map_add, hde, derivative_neg_exp, hCm1]
    ring
  rw [e1]
  ring

theorem cosh_sq_sub_sinh_sq : coshPS ^ 2 - sinhPS ^ 2 = 1 := by
  have haf := exp_neg_mul
  have h2C : (2 : PowerSeries ℚ) * PowerSeries.C (2⁻¹ : ℚ) = 1 := by
    rw [mul_comm]; exact hCinv
  have hC : 4 * PowerSeries.C (2⁻¹ : ℚ) ^ 2 = 1 := by
    have hrw : 4 * PowerSeries.C (2⁻¹ : ℚ) ^ 2 =
        ((2 : PowerSeries ℚ) * PowerSeries.C (2⁻¹ : ℚ)) *
          ((2 : PowerSeries ℚ) * PowerSeries.C (2⁻¹ : ℚ)) := by ring
    rw [hrw, h2C, mul_one]
  have e : (coshPS ^ 2 - sinhPS ^ 2) =
      (PowerSeries.exp ℚ * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
        (4 * PowerSeries.C (2⁻¹ : ℚ) ^ 2) := by
    unfold coshPS sinhPS
    ring
  rw [e, haf, one_mul]
  exact hC

theorem derivative_euler :
    PowerSeries.derivative eulerEGF = -(eulerEGF ^ 2 * sinhPS) := by
  have h1 : eulerEGF * coshPS = 1 := euler_cosh
  have hL : eulerEGF * sinhPS + coshPS * PowerSeries.derivative eulerEGF = 0 := by
    have h0 : PowerSeries.derivative (eulerEGF * coshPS) = 0 := by
      rw [h1, ← map_one PowerSeries.C]
      exact PowerSeries.derivative_C
    rw [Derivation.leibniz, derivative_cosh] at h0
    simp only [smul_eq_mul] at h0
    -- h0 : E * sinh + cosh * E' = 0 (up to order)
    linear_combination h0
  have h3 : eulerEGF ^ 2 * sinhPS + PowerSeries.derivative eulerEGF = 0 := by
    linear_combination eulerEGF * hL - PowerSeries.derivative eulerEGF * h1
  have hE' : PowerSeries.derivative eulerEGF = -(eulerEGF ^ 2 * sinhPS) := by
    linear_combination h3
  exact hE'

theorem derivative_tanh : PowerSeries.derivative tanhPS = eulerEGF ^ 2 := by
  have h1 : eulerEGF * coshPS = 1 := euler_cosh
  have hE2 : eulerEGF ^ 2 * coshPS ^ 2 = 1 := by
    have hE2c : (eulerEGF * coshPS) ^ 2 = 1 := by rw [h1, one_pow]
    rwa [mul_pow] at hE2c
  have hsq2 : eulerEGF ^ 2 * coshPS ^ 2 - eulerEGF ^ 2 * sinhPS ^ 2 = eulerEGF ^ 2 := by
    have hsq := cosh_sq_sub_sinh_sq
    have hdist : eulerEGF ^ 2 * (coshPS ^ 2 - sinhPS ^ 2) = eulerEGF ^ 2 := by
      rw [hsq, mul_one]
    rwa [mul_sub] at hdist
  unfold tanhPS
  rw [Derivation.leibniz, derivative_sinh]
  simp only [smul_eq_mul]
  rw [derivative_euler, h1]
  linear_combination hsq2 - hE2

theorem derivative_XT :
    PowerSeries.derivative (PowerSeries.X * tanhPS) =
      tanhPS + PowerSeries.X * eulerEGF ^ 2 := by
  rw [Derivation.leibniz, derivative_tanh]
  simp only [smul_eq_mul, PowerSeries.derivative_X, mul_one]
  ring

theorem coeff_E_sq (m : ℕ) :
    PowerSeries.coeff (2 * m) (eulerEGF ^ 2) =
      (∑ k ∈ Finset.range (m + 1),
        ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
          ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
        ((2 * m).factorial : ℚ) := by
  have hant : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal (2 * m),
        PowerSeries.coeff p.1 eulerEGF * PowerSeries.coeff p.2 eulerEGF) =
      ∑ k ∈ Finset.range (2 * m + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (2 * m - k) eulerEGF := by
    have h := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i eulerEGF * PowerSeries.coeff j eulerEGF) (2 * m)
    simpa using h
  rw [sq, PowerSeries.coeff_mul, hant]
  have hsum : ∑ k ∈ Finset.range (2 * m + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (2 * m - k) eulerEGF =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (2 * m - 2 * j) eulerEGF := by
    apply sum_range_two_mul_succ
    intro k hkodd
    rw [coeff_eulerEGF, ite_eq_left (Nat.odd_iff.mp hkodd), zero_mul]
  rw [hsum]
  have hterm : ∀ j ∈ Finset.range (m + 1),
      PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (2 * m - 2 * j) eulerEGF =
        (((Nat.choose (2 * m) (2 * j) : ℕ) : ℚ) *
          ((chapter5EulerEven j : ℤ) : ℚ) * ((chapter5EulerEven (m - j) : ℤ) : ℚ)) /
          ((2 * m).factorial : ℚ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjm : j ≤ m := by omega
    have h2jm : 2 * j ≤ 2 * m := by omega
    have hj2 : (2 * j) / 2 = j := by omega
    have hjm2 : (2 * m - 2 * j) / 2 = m - j := by omega
    have hmod1 : ¬ ((2 * j) % 2 = 1) := by omega
    have hmod2 : ¬ ((2 * m - 2 * j) % 2 = 1) := by omega
    rw [coeff_eulerEGF, ite_eq_right hmod1, hj2, coeff_eulerEGF, ite_eq_right hmod2, hjm2]
    have hchoose := Nat.choose_mul_factorial_mul_factorial h2jm
    have hcast : ((Nat.choose (2 * m) (2 * j) : ℕ) : ℚ) * (((2 * j).factorial : ℕ) : ℚ) *
        (((2 * m - 2 * j).factorial : ℕ) : ℚ) = (((2 * m).factorial : ℕ) : ℚ) := by
      exact_mod_cast hchoose
    have hd1 : (((2 * j).factorial : ℕ) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * j)
    have hd2 : ((((2 * m - 2 * j).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m - 2 * j)
    have hfact : ((((2 * m).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m)
    have hAB : ((((2 * j).factorial : ℕ) : ℚ) * ((((2 * m - 2 * j).factorial : ℕ)) : ℚ)) ≠ 0 :=
      mul_ne_zero hd1 hd2
    rw [div_mul_div_comm, div_eq_div_iff hAB hfact]
    linear_combination -(((chapter5EulerEven j : ℤ) : ℚ) *
      ((chapter5EulerEven (m - j) : ℤ) : ℚ)) * hcast
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]

theorem coeff_XT_bernoulli (n : ℕ) (_hn : 1 ≤ n) :
    PowerSeries.coeff (2 * n) (PowerSeries.X * tanhPS) =
      (((4 : ℚ) ^ (2 * n) - (2 : ℚ) ^ (2 * n)) * bernoulli (2 * n)) /
        (((2 * n).factorial : ℕ) : ℚ) := by
  have hXT := bernoulli_tanh
  have h21 : 2 * n ≠ 1 := by omega
  have hX0 : PowerSeries.coeff (2 * n) (PowerSeries.X : PowerSeries ℚ) = 0 := by
    rw [PowerSeries.coeff_X, ite_eq_right h21]
  have h4 : PowerSeries.coeff (2 * n) berB4 =
      (4 : ℚ) ^ (2 * n) * (bernoulli (2 * n) / (((2 * n).factorial : ℕ) : ℚ)) := by
    unfold berB4
    rw [PowerSeries.coeff_rescale, berB_coeff]
  have h2 : PowerSeries.coeff (2 * n) berB2 =
      (2 : ℚ) ^ (2 * n) * (bernoulli (2 * n) / (((2 * n).factorial : ℕ) : ℚ)) := by
    unfold berB2
    rw [PowerSeries.coeff_rescale, berB_coeff]
  have hcoeff : PowerSeries.coeff (2 * n) (PowerSeries.X * tanhPS) =
      PowerSeries.coeff (2 * n) (PowerSeries.X + berB4 - berB2) := by rw [hXT]
  rw [hcoeff]
  simp only [map_add, map_sub, hX0, h4, h2]
  ring

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 5.

Proves `Wanted` entry `ramanujan_part1_ch5_entry10b_euleriansymmetry`.
-/
theorem ramanujan_part1_ch5_entry10b_euleriansymmetry (n : ℕ) :
    (2 : ℚ) ^ (2 * n) * ((2 : ℚ) ^ (2 * n) - 1) * bernoulli (2 * n) =
      ((2 * n : ℕ) : ℚ) *
        ∑ k ∈ range n,
          (Nat.choose (2 * n - 2) (2 * k) : ℚ) *
            (chapter5EulerEven k : ℚ) *
              (chapter5EulerEven (n - k - 1) : ℚ) := by
  cases n with
  | zero =>
    simp [bernoulli_zero]
  | succ m =>
    have hFne : ((((2 * (m + 1)).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * (m + 1))
    have hF2ne : ((((2 * m).factorial : ℕ)) : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * m)
    have hNNne : ((((2 * (m + 1) : ℕ)))) ≠ (0 : ℚ) := by
      exact_mod_cast (by omega : 2 * (m + 1) ≠ 0)
    have hN1ne : ((((2 * (m + 1) - 1 : ℕ)))) ≠ (0 : ℚ) := by
      exact_mod_cast (by omega : 2 * (m + 1) - 1 ≠ 0)
    -- Bernoulli side
    have cA : PowerSeries.coeff (2 * (m + 1)) (PowerSeries.X * tanhPS) =
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) :=
      coeff_XT_bernoulli (m + 1) (by omega)
    -- derivative equation at level 2(m+1)-1
    have hA' := derivative_XT
    have e_deriv : PowerSeries.coeff (2 * (m + 1) - 1)
          (PowerSeries.derivative (PowerSeries.X * tanhPS)) =
        PowerSeries.coeff (2 * (m + 1) - 1) tanhPS +
          PowerSeries.coeff (2 * (m + 1) - 1) (PowerSeries.X * eulerEGF ^ 2) := by
      rw [hA']
      exact map_add _ _ _
    have cAd : PowerSeries.coeff (2 * (m + 1) - 1)
          (PowerSeries.derivative (PowerSeries.X * tanhPS)) =
        PowerSeries.coeff (2 * (m + 1)) (PowerSeries.X * tanhPS) *
          (((2 * (m + 1) : ℕ)) : ℚ) := by
      rw [PowerSeries.coeff_derivative]
      have h1 : 2 * (m + 1) - 1 + 1 = 2 * (m + 1) := by omega
      rw [h1]
      have hsub : ((2 * (m + 1) - 1 : ℕ) : ℚ) + 1 = ((2 * (m + 1) : ℕ) : ℚ) := by
        rw [Nat.cast_sub (show 1 ≤ 2 * (m + 1) by omega), Nat.cast_one, sub_add_cancel]
      rw [hsub]
    have cT : PowerSeries.coeff (2 * (m + 1) - 1) tanhPS =
        PowerSeries.coeff (2 * (m + 1)) (PowerSeries.X * tanhPS) := by
      have h := PowerSeries.coeff_succ_X_mul (2 * (m + 1) - 1) tanhPS
      have h1 : 2 * (m + 1) - 1 + 1 = 2 * (m + 1) := by omega
      rw [h1] at h
      exact h.symm
    have cE : PowerSeries.coeff (2 * (m + 1) - 1) (PowerSeries.X * eulerEGF ^ 2) =
        (∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
            ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
          ((((2 * m).factorial : ℕ)) : ℚ) := by
      have h0 : PowerSeries.coeff (2 * (m + 1) - 1) (PowerSeries.X * eulerEGF ^ 2) =
          PowerSeries.coeff (2 * (m + 1) - 2) (eulerEGF ^ 2) := by
        have h := PowerSeries.coeff_succ_X_mul (2 * (m + 1) - 2) (eulerEGF ^ 2)
        have h1 : 2 * (m + 1) - 2 + 1 = 2 * (m + 1) - 1 := by omega
        rw [h1] at h
        exact h
      rw [h0]
      have hm2 : 2 * (m + 1) - 2 = 2 * m := by omega
      rw [hm2, coeff_E_sq]
    -- combined equation
    have eq : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) *
          ((((2 * (m + 1) : ℕ)))) =
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) +
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
            ((((2 * m).factorial : ℕ)) : ℚ) := by
      rw [← cA, ← cAd, ← cT, ← cE]
      exact e_deriv
    -- factorial relation
    have hfactQ : ((((2 * (m + 1)).factorial : ℕ)) : ℚ) =
        ((((2 * (m + 1) : ℕ)))) * ((((2 * (m + 1) - 1 : ℕ)))) *
          ((((2 * m).factorial : ℕ)) : ℚ) := by
      have e1 : 2 * (m + 1) = 2 * m + 2 := by omega
      have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have hfactN : (2 * m + 2).factorial = (2 * m + 2) * (2 * m + 1) * (2 * m).factorial := by
        have s1 : 2 * m + 2 = (2 * m + 1) + 1 := by omega
        conv_lhs => rw [s1]
        rw [Nat.factorial_succ]
        have f2 : ((2 * m + 1)).factorial = (2 * m + 1) * (2 * m).factorial := by
          have t : 2 * m + 1 = (2 * m) + 1 := by omega
          conv_lhs => rw [t]
          rw [Nat.factorial_succ]
        rw [f2]
        ring
      rw [e2, e1]
      exact_mod_cast hfactN
    -- N - 1 = N1
    have hNN1 : ((((2 * (m + 1) : ℕ)) : ℚ)) - 1 =
        ((((2 * (m + 1) - 1 : ℕ)) : ℚ)) := by
      rw [Nat.cast_sub (show 1 ≤ 2 * (m + 1) by omega), Nat.cast_one]
    -- clear denominators
    have hP : (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ))))) *
          (((((2 * (m + 1)).factorial : ℕ)) : ℚ) * (((2 * m).factorial : ℕ) : ℚ)) =
        (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * (((2 * m).factorial : ℕ) : ℚ) +
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            (((2 * (m + 1)).factorial : ℕ) : ℚ)) *
          (((2 * (m + 1)).factorial : ℕ) : ℚ) := by
      have eB : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) *
            ((((2 * (m + 1) : ℕ)))) =
          (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ))))) /
            (((2 * (m + 1)).factorial : ℕ) : ℚ) :=
        div_mul_eq_mul_div _ _ _
      have eA : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) / (((2 * (m + 1)).factorial : ℕ) : ℚ) +
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) /
            ((((2 * m).factorial : ℕ)) : ℚ) =
          (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * (((2 * m).factorial : ℕ) : ℚ) +
            (∑ k ∈ Finset.range (m + 1),
              ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
                ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
              (((2 * (m + 1)).factorial : ℕ) : ℚ)) /
            (((((2 * (m + 1)).factorial : ℕ)) : ℚ) * (((2 * m).factorial : ℕ) : ℚ)) := by
        rw [div_add_div _ _ hFne hF2ne]
        ring
      rw [eB, eA] at eq
      have h := (div_eq_div_iff hFne (mul_ne_zero hFne hF2ne)).mp eq
      linear_combination h
    -- factor out F
    have hX : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ)))) *
          ((((2 * m).factorial : ℕ)) : ℚ) -
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * m).factorial : ℕ)) : ℚ) -
        (∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
            ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
          (((2 * (m + 1)).factorial : ℕ) : ℚ) = 0 := by
      have hFX : ((((2 * (m + 1)).factorial : ℕ)) : ℚ) *
          (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ)))) *
            ((((2 * m).factorial : ℕ)) : ℚ) -
          ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) * ((((2 * m).factorial : ℕ)) : ℚ) -
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            (((2 * (m + 1)).factorial : ℕ) : ℚ)) = 0 := by
        linear_combination hP
      rcases mul_eq_zero.mp hFX with h | h
      · exact absurd h hFne
      · exact h
    rw [hfactQ] at hX
    have hXf : ((((2 * m).factorial : ℕ)) : ℚ) *
        (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) * ((((2 * (m + 1) : ℕ)))) -
        ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1))) -
        (∑ k ∈ Finset.range (m + 1),
          ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
            ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
          ((((2 * (m + 1) : ℕ)))) * ((((2 * (m + 1) - 1 : ℕ)))) ) = 0 := by
      linear_combination hX
    rcases mul_eq_zero.mp hXf with h | h
    · exact absurd h hF2ne
    · have hG0 : (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) -
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            ((((2 * (m + 1) : ℕ))))) * ((((2 * (m + 1) - 1 : ℕ)))) = 0 := by
        linear_combination h - (((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
          bernoulli (2 * (m + 1)))) * hNN1
      rcases mul_eq_zero.mp hG0 with h2 | h2
      · have hbS : ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
            bernoulli (2 * (m + 1))) =
          (∑ k ∈ Finset.range (m + 1),
            ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
              ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) *
            ((((2 * (m + 1) : ℕ)))) :=
          sub_eq_zero.mp h2
        have h42 : (4 : ℚ) ^ (2 * (m + 1)) = (2 : ℚ) ^ (2 * (m + 1)) * (2 : ℚ) ^ (2 * (m + 1)) := by
          rw [show (4 : ℚ) = 2 * 2 from by ring, mul_pow]
        have hLHS : (2 : ℚ) ^ (2 * (m + 1)) *
              ((2 : ℚ) ^ (2 * (m + 1)) - 1) * bernoulli (2 * (m + 1)) =
            ((((4 : ℚ) ^ (2 * (m + 1)) - (2 : ℚ) ^ (2 * (m + 1)))) *
              bernoulli (2 * (m + 1))) := by
          rw [h42]
          ring
        have hSsum : (∑ k ∈ Finset.range (m + 1),
              (Nat.choose (2 * (m + 1) - 2) (2 * k) : ℚ) *
                (chapter5EulerEven k : ℚ) *
                  (chapter5EulerEven ((m + 1) - k - 1) : ℚ)) =
            (∑ k ∈ Finset.range (m + 1),
              ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) *
                ((chapter5EulerEven k : ℤ) : ℚ) * ((chapter5EulerEven (m - k) : ℤ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          have e1 : 2 * (m + 1) - 2 = 2 * m := by omega
          have e2 : (m + 1) - k - 1 = m - k := by omega
          rw [e1, e2]
        rw [hLHS, hSsum, hbS]
        ring
      · exact absurd h2 hN1ne

end
end Entry10bEuleriansymmetry
end Ramanujan.Part1Ch5
end
