/-
Author: @akiezun, Avocado
-/

import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Def.Analysis.SpecialFunctions.Part1Ch5Entry10bEuleriansymmetry.Part2
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

theorem coeff_eulerEGF (n : ℕ) :
    PowerSeries.coeff n eulerEGF =
      if n % 2 = 1 then 0
      else (((chapter5EulerEven (n / 2) : ℤ) : ℚ) / (n.factorial : ℚ)) := by
  simp [eulerEGF, PowerSeries.coeff_mk]

theorem coeff_coshPS (n : ℕ) :
    PowerSeries.coeff n coshPS =
      (if n % 2 = 0 then (1 : ℚ) / (n.factorial : ℚ) else 0) := by
  unfold coshPS
  rw [PowerSeries.coeff_mul_C]
  have h1 : PowerSeries.coeff n
      (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      (1 : ℚ) / (n.factorial : ℚ) + (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
    have e1 : PowerSeries.coeff n (PowerSeries.exp ℚ) = (1 : ℚ) / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_exp]; simp
    have e2 : PowerSeries.coeff n ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
        (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp [div_eq_mul_inv]
    rw [map_add, e1, e2]
  rw [h1]
  by_cases hn : n % 2 = 0
  · have hpow : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.mpr hn)
    simp [hn, hpow]
    field_simp
    ring
  · have hodd : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    simp only [hn, hodd, ↓reduceIte]
    have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring

theorem coeff_sinhPS (n : ℕ) :
    PowerSeries.coeff n sinhPS =
      (if n % 2 = 1 then (1 : ℚ) / (n.factorial : ℚ) else 0) := by
  unfold sinhPS
  rw [PowerSeries.coeff_mul_C]
  have h1 : PowerSeries.coeff n
      (PowerSeries.exp ℚ - (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      (1 : ℚ) / (n.factorial : ℚ) - (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
    have e1 : PowerSeries.coeff n (PowerSeries.exp ℚ) = (1 : ℚ) / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_exp]; simp
    have e2 : PowerSeries.coeff n ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
        (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp [div_eq_mul_inv]
    rw [map_sub, e1, e2]
  rw [h1]
  by_cases hn : n % 2 = 1
  · have hpow : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr hn)
    simp [hn, hpow]
    field_simp
    ring
  · have hpow : (-1 : ℚ) ^ n = 1 := by
      have hev : Even n := Nat.even_iff.mpr (by omega)
      exact Even.neg_one_pow hev
    simp [hn, hpow]

theorem euler_cosh : eulerEGF * coshPS = 1 := by
  ext n
  have hant : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff p.1 eulerEGF * PowerSeries.coeff p.2 coshPS) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (n - k) coshPS := by
    have h := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i eulerEGF * PowerSeries.coeff j coshPS) n
    simpa using h
  rw [PowerSeries.coeff_mul, hant, PowerSeries.coeff_one]
  by_cases hn : n % 2 = 1
  · have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hkle : k ≤ n := by omega
    by_cases hk2 : k % 2 = 1
    · rw [coeff_eulerEGF, ite_eq_left hk2, zero_mul]
    · have hnk : (n - k) % 2 = 1 := by omega
      have hne : ¬ ((n - k) % 2 = 0) := by omega
      rw [coeff_coshPS, ite_eq_right hne, mul_zero]
  · have hn0 : n % 2 = 0 := by omega
    -- n even; write n = 2 * (n/2)
    have hn2 : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even (Nat.even_iff.mpr hn0)).symm
    have hfact_n : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    -- restrict to even indices
    have hsum : ∑ k ∈ Finset.range (n + 1),
          PowerSeries.coeff k eulerEGF * PowerSeries.coeff (n - k) coshPS =
        ∑ j ∈ Finset.range (n / 2 + 1),
          PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (n - 2 * j) coshPS := by
      have hnr : n + 1 = 2 * (n / 2) + 1 := by omega
      rw [hnr]
      apply sum_range_two_mul_succ
      intro k hkodd
      rw [coeff_eulerEGF, ite_eq_left (Nat.odd_iff.mp hkodd), zero_mul]
    rw [hsum]
    -- each term equals choose * Euler / n!
    have hterm : ∀ j ∈ Finset.range (n / 2 + 1),
        PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (n - 2 * j) coshPS =
        (((Nat.choose n (2 * j) : ℕ) : ℚ) * ((chapter5EulerEven j : ℤ) : ℚ)) /
          (n.factorial : ℚ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjn : 2 * j ≤ n := by omega
      have hj2 : (2 * j) / 2 = j := by omega
      have hjm : n - 2 * j = 2 * (n / 2 - j) := by omega
      have hmod1 : ¬ ((2 * j) % 2 = 1) := by omega
      have hmod2 : (n - 2 * j) % 2 = 0 := by omega
      rw [coeff_eulerEGF, ite_eq_right hmod1, coeff_coshPS, ite_eq_left hmod2, hj2]
      have hchoose := Nat.choose_mul_factorial_mul_factorial hjn
      have hfact1 : ((j.factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      -- (2j)! = j-th factorial appearing via hj2? need (2*j)! vs j! confusion:
      -- e_{2j} denominator is ((2*j)!), c denominator is ((n-2j)!).
      -- Combine into C(n,2j)/n!.
      have hcast : ((Nat.choose n (2 * j) : ℕ) : ℚ) * (((2 * j).factorial : ℕ) : ℚ) *
          (((n - 2 * j).factorial : ℕ) : ℚ) = ((n.factorial : ℕ) : ℚ) := by
        exact_mod_cast hchoose
      have hd1 : (((2 * j).factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * j)
      have hd2 : ((((n - 2 * j).factorial : ℕ)) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n - 2 * j)
      have hAB : ((((2 * j).factorial : ℕ) : ℚ) * ((((n - 2 * j).factorial : ℕ)) : ℚ)) ≠ 0 :=
        mul_ne_zero hd1 hd2
      rw [div_mul_div_comm, mul_one, div_eq_div_iff hAB hfact_n]
      linear_combination -((chapter5EulerEven j : ℤ) : ℚ) * hcast
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_div]
    have hrec := eulerEven_recurrenceQ (n / 2)
    rw [← hn2] at hrec
    by_cases hm : n / 2 = 0
    · have hn00 : n = 0 := by omega
      subst hn00
      simp only [Nat.zero_div, zero_add, range_one, sum_singleton, mul_zero,
        Nat.choose_self, Nat.cast_one, one_mul, Nat.factorial_zero, div_one,
        ↓reduceIte, Rat.intCast_eq_one_iff] at hrec ⊢
      rw [hrec]
    · have hn00 : n ≠ 0 := by omega
      simp only [hm, hn00, ↓reduceIte] at hrec ⊢
      rw [hrec]
      simp

-- Bernoulli / exponential facts
theorem exp_neg_mul :
    PowerSeries.exp ℚ * (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ) = 1 := by
  have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 1 (-1)
  have h1 : (1 : ℚ) + (-1) = 0 := by ring
  rw [h1] at h
  have hr1 : (PowerSeries.rescale (1 : ℚ)) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
    simp [PowerSeries.rescale_one]
  rw [hr1] at h
  have h0 : (PowerSeries.rescale (0 : ℚ)) (PowerSeries.exp ℚ) = 1 := by
    ext n
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, PowerSeries.coeff_one]
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn]
  rw [h0] at h
  exact h

theorem exp_sq2 :
    PowerSeries.exp ℚ ^ 2 = (PowerSeries.rescale (2 : ℚ)) (PowerSeries.exp ℚ) := by
  have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 1 1
  have hr1 : (PowerSeries.rescale (1 : ℚ)) (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
    simp [PowerSeries.rescale_one]
  rw [hr1] at h
  have h2 : (1 : ℚ) + 1 = 2 := by ring
  rw [h2] at h
  rw [sq]
  exact h

theorem exp_four :
    PowerSeries.exp ℚ ^ 4 = (PowerSeries.rescale (4 : ℚ)) (PowerSeries.exp ℚ) := by
  have ha2 := exp_sq2
  have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 2 2
  have h22 : (2 : ℚ) + 2 = 4 := by ring
  rw [h22] at h
  have hp : (PowerSeries.exp ℚ : PowerSeries ℚ) ^ 4 = ((PowerSeries.exp ℚ) ^ 2) ^ 2 := by ring
  rw [hp, ha2, sq]
  exact h

theorem cofactor2 (s u a f X : PowerSeries ℚ) :
    let A := a ^ 2 - 1
    let Bf := a ^ 4 - 1
    let R1 := s * Bf - 4 * X
    let R2 := u * A - 2 * X
    let R5 := a * f - 1
    let G := (X + s - u) * (a + f) - X * (a - f)
    let M := A * Bf
    G * M = (a + f) * A * R1 - (a + f) * Bf * R2 +
      (X * (2 * a * A ^ 2)) * R5 := by
  simp only
  ring

theorem C4_eq : PowerSeries.C (4 : ℚ) = (4 : PowerSeries ℚ) := map_ofNat _ _

theorem C2_eq : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := map_ofNat _ _

end
end Entry10bEuleriansymmetry
end Ramanujan.Part1Ch5
end
