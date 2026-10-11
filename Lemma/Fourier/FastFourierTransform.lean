import Mathlib
import sympy.Basic
import sympy.integrals.transforms.FastFourierTransform

open Fourier.FastFourierTransformWanted

/--
[dftSum_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma dft_sum_two_mul_eq
-- given
  (n : ℕ)
  (ω : ℂ)
  (f : ℕ → ℂ)
  (K : ℕ) :
-- imply
  dftSum (2 * n) ω f K =
    dftSum n (ω ^ 2) (fun t => f (2 * t)) K +
      ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) K := by
-- proof
  apply dftSum_two_mul n ω f K

/--
[dftSum_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma dft_sum_mod_eq
-- given
  (n : ℕ)
  (ω : ℂ)
  (hω : ω ^ n = 1)
  (f : ℕ → ℂ)
  (K : ℕ) :
-- imply
  dftSum n ω f K = dftSum n ω f (K % n) := by
-- proof
  apply dftSum_mod n ω hω f K

/--
[cooley_tukey](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma cooley_tukey_eq
-- given
  (n : ℕ)
  (ω : ℂ)
  (hω : ω ^ (2 * n) = 1)
  (f : ℕ → ℂ)
  (K : ℕ) :
-- imply
  dftSum (2 * n) ω f K =
    dftSum n (ω ^ 2) (fun t => f (2 * t)) (K % n) +
      ω ^ K * dftSum n (ω ^ 2) (fun t => f (2 * t + 1)) (K % n) := by
-- proof
  apply cooley_tukey n ω hω f K

/--
[fftCost_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/FastFourierTransform.lean)
-/
@[path]
private lemma fft_cost_recurrence_eq
-- given
  (n : ℕ)
  (hn : 0 < n) :
-- imply
  fftCost (2 * n) = 2 * fftCost n + 2 * n := by
-- proof
  apply fftCost_recurrence n hn

-- created on 2026-10-10
