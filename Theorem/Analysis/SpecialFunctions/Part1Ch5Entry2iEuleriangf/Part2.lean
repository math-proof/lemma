/-
Author: @akiezun, Avocado
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Squarefree
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Abbrev.Analysis.SpecialFunctions.Part1Ch5Entry2iEuleriangf
/-!
# Ramanujan's Notebooks, Part I, Chapter 5

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch5

namespace Entry2iEuleriangf

open scoped Nat Real BigOperators Interval Polynomial

open Finset

noncomputable section

theorem neg_one_sq_pow (m : ℕ) : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
  rw [sq, ← pow_add, ← two_mul]
  exact Even.neg_one_pow ⟨m, two_mul m⟩

theorem neg_one_pow_mul_self (m : ℕ) : (-1 : ℝ) ^ m * (-1) ^ m = 1 := by
  rw [← pow_add, show m + m = 2 * m from by ring]
  exact Even.neg_one_pow ⟨m, two_mul m⟩

theorem neg_one_sub_pow (i j : ℕ) (h : j ≤ i) :
    (-1 : ℝ) ^ (i - j) = (-1) ^ i * (-1) ^ j := by
  have h2 : (-1 : ℝ) ^ (i - j) * (-1) ^ j = (-1) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel h]
  calc (-1 : ℝ) ^ (i - j) = (-1 : ℝ) ^ (i - j) * (((-1) ^ j) ^ 2) := by
        rw [neg_one_sq_pow, mul_one]
    _ = ((-1 : ℝ) ^ (i - j) * (-1) ^ j) * (-1) ^ j := by ring
    _ = (-1) ^ i * (-1) ^ j := by rw [h2]

theorem scalar_match_upper (n k : ℕ) (hk : k ≤ n) :
    ((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      ((2 * n).choose (n + k) : ℝ) * (-1 : ℝ) ^ (2 * n - (n + k)) =
      (-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
        (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  have hle : n + k ≤ 2 * n := by omega
  have hsub : 2 * n - (n + k) = n - k := by omega
  have key : ((2 * n).choose (n + k) : ℝ) * ((n + k).factorial : ℝ) *
      ((n - k).factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : 2 * n - (n + k) = n - k := by omega
    rw [h2] at h
    exact_mod_cast h
  have hF1 : ((n + k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hsub, neg_one_sub_pow n k hk,
    show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
      ((2 * n).choose (n + k) : ℝ) * ((-1 : ℝ) ^ n * (-1) ^ k)
      = ((n.factorial : ℝ) ^ 2 * ((2 * n).choose (n + k) : ℝ) * (-1 : ℝ) ^ k /
        ((2 * n).factorial : ℝ)) * ((-1 : ℝ) ^ n * (-1) ^ n) from by ring,
    neg_one_pow_mul_self n, mul_one]
  field_simp
  linear_combination key

theorem scalar_match_lower (n k : ℕ) (hk : k ≤ n) :
    ((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      ((2 * n).choose (n - k) : ℝ) * (-1 : ℝ) ^ (2 * n - (n - k)) =
      (-1 : ℝ) ^ k * ((n.factorial : ℝ) ^ 2) /
        (((n + k).factorial : ℝ) * ((n - k).factorial : ℝ)) := by
  have hle : n - k ≤ 2 * n := by omega
  have hsub : 2 * n - (n - k) = n + k := by omega
  have key : ((2 * n).choose (n - k) : ℝ) * ((n - k).factorial : ℝ) *
      ((n + k).factorial : ℝ) = ((2 * n).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have h2 : 2 * n - (n - k) = n + k := by omega
    rw [h2] at h
    exact_mod_cast h
  have hF1 : ((n + k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF2 : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hsub, pow_add,
    show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
      ((2 * n).choose (n - k) : ℝ) * ((-1 : ℝ) ^ n * (-1) ^ k)
      = ((n.factorial : ℝ) ^ 2 * ((2 * n).choose (n - k) : ℝ) * (-1 : ℝ) ^ k /
        ((2 * n).factorial : ℝ)) * ((-1 : ℝ) ^ n * (-1) ^ n) from by ring,
    neg_one_pow_mul_self n, mul_one]
  field_simp
  linear_combination key

theorem scalar_match_center (n : ℕ) :
    ((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
      ((2 * n).choose n : ℝ) * (-1 : ℝ) ^ (2 * n - n) = 1 := by
  have hsub : 2 * n - n = n := by omega
  have key : ((2 * n).choose n : ℝ) * ((n.factorial : ℝ)) *
      ((n.factorial : ℝ)) = ((2 * n).factorial : ℝ) := by
    have h := Nat.add_choose_mul_factorial_mul_factorial n n
    have h2 : n + n = 2 * n := by ring
    rw [h2] at h
    exact_mod_cast h
  have hF1 : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((2 * n).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hsub,
    show (-1 : ℝ) ^ n * (n.factorial : ℝ) ^ 2 / ((2 * n).factorial : ℝ) *
      ((2 * n).choose n : ℝ) * (-1 : ℝ) ^ n
      = ((n.factorial : ℝ) ^ 2 * ((2 * n).choose n : ℝ) /
        ((2 * n).factorial : ℝ)) * ((-1 : ℝ) ^ n * (-1) ^ n) from by ring,
    neg_one_pow_mul_self n, mul_one]
  field_simp
  linear_combination key

theorem sum_range_two_mul_add_one_eq {A : Type*} [AddCommMonoid A] (G : ℕ → A) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n + 1), G j =
      G n + ∑ k ∈ Finset.Icc 1 n, (G (n + k) + G (n - k)) := by
  have h1 : 2 * n + 1 = n + (n + 1) := by omega
  rw [h1, Finset.sum_range_add, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have hrefl : ∑ k ∈ Finset.range n, G k = ∑ k ∈ Finset.range n, G (n - (k + 1)) := by
    have h := Finset.sum_range_reflect (fun k => G (n - (k + 1))) n
    rw [← h]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    congr 1
    omega
  rw [hrefl]
  have hIcc : (∑ k ∈ Finset.Icc 1 n, (G (n + k) + G (n - k))) =
      ∑ k ∈ Finset.range n, (G (n + (k + 1)) + G (n - (k + 1))) := by
    have : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := rfl
    rw [this, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm 1 k]
  rw [hIcc, Finset.sum_add_distrib]
  ac_rfl

theorem sym_shift_identity {A : Type*} [CommRing A] {a b : A} (hab : a * b = 1) :
    a + b - 2 = b * (a - 1) ^ 2 := by
  linear_combination (2 - a) * hab

theorem n7_expand {A : Type*} [CommRing A] [Algebra ℝ A] (a b : A) (hab : a * b = 1)
    (n : ℕ) :
    (((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) • (a + b - 2) ^ n) =
      ∑ j ∈ Finset.range (2 * n + 1),
        ((((-1 : ℝ) ^ n * ((n.factorial : ℝ) ^ 2) / ((2 * n).factorial : ℝ)) *
          (((2 * n).choose j : ℝ)) * (-1 : ℝ) ^ (2 * n - j)) • (a ^ j * b ^ n)) := by
  have hexp : (a - 1) ^ (2 * n) =
      ∑ j ∈ Finset.range (2 * n + 1),
          (a ^ j * (-1 : A) ^ (2 * n - j) * (((2 * n).choose j : A))) := by
    rw [sub_eq_add_neg]
    exact add_pow a (-1) (2 * n)
  rw [sym_shift_identity hab, mul_pow, ← pow_mul, hexp, Finset.mul_sum, smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have e1 : (-1 : A) ^ (2 * n - j) = algebraMap ℝ A ((-1 : ℝ) ^ (2 * n - j)) := by
    simp [map_pow]
  have e2 : (((2 * n).choose j : A)) = algebraMap ℝ A ((((2 * n).choose j : ℝ))) :=
    (map_natCast (algebraMap ℝ A) ((2 * n).choose j)).symm
  rw [e1, e2, mul_assoc (a ^ j) _ _, (map_mul (algebraMap ℝ A) _ _).symm]
  have hcomm : b ^ n * (a ^ j * algebraMap ℝ A ((-1 : ℝ) ^ (2 * n - j) * (((2 * n).choose j : ℝ))))
      = algebraMap ℝ A ((-1 : ℝ) ^ (2 * n - j) * (((2 * n).choose j : ℝ))) * (a ^ j * b ^ n) := by
    ring
  rw [hcomm, Algebra.smul_def, Algebra.smul_def, ← mul_assoc, (map_mul (algebraMap ℝ A) _ _).symm]
  congr 1
  ring_nf

theorem aeval_derivative_apply_eq_zero {p phi : ℝ[X]} {m : ℕ}
    (hdvd : Polynomial.X ^ m ∣ p) (hlt : phi.natDegree < m) :
    (Polynomial.aeval Polynomial.derivative) p phi = 0 := by
  obtain ⟨q, rfl⟩ := hdvd
  have h0 : (⇑Polynomial.derivative)^[m] phi = 0 := Polynomial.iterate_derivative_eq_zero hlt
  rw [mul_comm, map_mul, Polynomial.aeval_X_pow, Module.End.mul_apply, Module.End.pow_apply,
    h0, map_zero]

theorem aeval_derivative_apply_eq_of_sub {p q phi : ℝ[X]} {m : ℕ}
    (hdvd : Polynomial.X ^ m ∣ p - q) (hlt : phi.natDegree < m) :
    (Polynomial.aeval Polynomial.derivative) p phi = (Polynomial.aeval Polynomial.derivative) q
        phi := by
  have h : (Polynomial.aeval Polynomial.derivative) (p - q) phi = 0 :=
    aeval_derivative_apply_eq_zero hdvd hlt
  rw [map_sub, LinearMap.sub_apply] at h
  exact sub_eq_zero.mp h

theorem natDegree_aeval_derivative_apply_le (p phi : ℝ[X]) :
    ((Polynomial.aeval Polynomial.derivative) p phi).natDegree ≤ phi.natDegree := by
  rw [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [LinearMap.smul_apply, Module.End.pow_apply]
  exact le_trans (Polynomial.natDegree_smul_le _ _)
    (le_trans (Polynomial.natDegree_iterate_derivative phi i) (Nat.sub_le _ _))

theorem x_pow_succ_dvd_of_derivative {g : PowerSeries ℝ} {m : ℕ}
    (h0 : PowerSeries.constantCoeff g = 0)
    (hdvd : PowerSeries.X ^ m ∣ PowerSeries.derivative g) :
    PowerSeries.X ^ (m + 1) ∣ g := by
  rw [PowerSeries.X_pow_dvd_iff] at hdvd ⊢
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact h0
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < m := by omega
    have h1 := hdvd k hk
    rw [PowerSeries.coeff_derivative] at h1
    have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1).resolve_right h2

end
end Entry2iEuleriangf
end Ramanujan.Part1Ch5
end
