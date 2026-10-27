/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Def.Analysis.Fourier.FastFourierTransform
open scoped BigOperators


namespace Fourier.FastFourierTransformWanted

theorem fft_sum_range_even_odd (g : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (2 * n), g j =
      (∑ t ∈ Finset.range n, g (2 * t)) + ∑ t ∈ Finset.range n, g (2 * t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.mul_succ, Finset.sum_range_succ]
    rw [ih]
    ac_rfl

theorem fft_pow_even (ω : ℂ) (t K : ℕ) :
    ω ^ ((2 * t) * K) = (ω ^ 2) ^ (t * K) := by
  rw [mul_assoc, pow_mul]

theorem fft_pow_odd (ω : ℂ) (t K : ℕ) :
    ω ^ ((2 * t + 1) * K) = ω ^ K * (ω ^ 2) ^ (t * K) := by
  rw [add_mul, one_mul, mul_assoc, add_comm, pow_add, pow_mul]

/-- Splits an even-length DFT sum into its even and odd samples. -/
public theorem dftSum_two_mul (n : ℕ) (ω : ℂ) (f : ℕ → ℂ) (K : ℕ) :
    dftSum (2 * n) ω f K =
      dftSum n (ω ^ 2) (fun t => f (2 * t)) K +
        ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) K := by
  unfold dftSum
  rw [fft_sum_range_even_odd]
  simp_rw [fft_pow_even, fft_pow_odd]
  rw [Finset.mul_sum]
  simp only [mul_assoc]

theorem fft_pow_mul_mod (a : ℂ) (n t K : ℕ) (ha : a ^ n = 1) :
    a ^ (t * K) = a ^ (t * (K % n)) := by
  have hat : (a ^ t) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ha, one_pow]
  calc
    a ^ (t * K) = (a ^ t) ^ K := pow_mul a t K
    _ = (a ^ t) ^ (K % n) := pow_eq_pow_mod K hat
    _ = a ^ (t * (K % n)) := (pow_mul a t (K % n)).symm

/-- A DFT sum at an `n`th root of unity depends only on the frequency modulo `n`. -/
public theorem dftSum_mod (n : ℕ) (ω : ℂ) (hω : ω ^ n = 1) (f : ℕ → ℂ) (K : ℕ) :
    dftSum n ω f K = dftSum n ω f (K % n) := by
  unfold dftSum
  apply Finset.sum_congr rfl
  intro t _
  rw [fft_pow_mul_mod ω n t K hω]

/--
Radix-2 Cooley–Tukey splitting: a length-`2n` transform is two length-`n`
transforms on the even and odd subsequences plus twiddle factors.

Sources: `undergrad.yaml`, section "Fourier transform", entry "fast Fourier
transform"; J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (decimation
in time).

Proves `Wanted` entry `cooley_tukey`.

Proof: Split the range into even and odd indices, rewrite the powers, and use
root-of-unity periodicity to reduce the frequency modulo `n`, as in the
section "The radix-2 DIT case" of Wikipedia, "Cooley–Tukey FFT algorithm".
-/
public theorem cooley_tukey (n : ℕ) (ω : ℂ) (hω : ω ^ (2 * n) = 1)
    (f : ℕ → ℂ) (K : ℕ) :
    dftSum (2 * n) ω f K =
      dftSum n (ω ^ 2) (fun t => f (2 * t)) (K % n) +
        ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) (K % n) := by
  have hω2 : (ω ^ 2) ^ n = 1 := by
    simpa only [pow_mul] using hω
  calc
    dftSum (2 * n) ω f K =
        dftSum n (ω ^ 2) (fun t => f (2 * t)) K +
          ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) K :=
      dftSum_two_mul n ω f K
    _ = dftSum n (ω ^ 2) (fun t => f (2 * t)) (K % n) +
        ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) (K % n) := by
      rw [dftSum_mod n (ω ^ 2) hω2 (fun t => f (2 * t)) K]
      rw [dftSum_mod n (ω ^ 2) hω2 (fun t => f (2 * t + 1)) K]

end Fourier.FastFourierTransformWanted
