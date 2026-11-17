/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Def.Analysis.Fourier.FastFourierTransform.Part2
open scoped BigOperators

public section

namespace Fourier.FastFourierTransformWanted

theorem fft_log_two_mul (n : ℕ) (hn : 0 < n) :
    Nat.log 2 (2 * n) = Nat.log 2 n + 1 := by
  simpa only [Nat.mul_comm] using
    Nat.log_mul_base (b := 2) (n := n) (by decide) (Nat.ne_of_gt hn)

/--
The `n log n` cost satisfies the radix-2 FFT recurrence.

Sources: `undergrad.yaml`, section "Fourier transform", entry "fast Fourier
transform"; J. W. Cooley and J. W. Tukey, Math. Comp. 19 (1965) (`n log n`
operation count).

Proves `Wanted` entry `fftCost_recurrence`.

Proof: Apply `Nat.log_mul_base` to `n * 2`, commute the factors, and expand
multiplication.
-/
public theorem fftCost_recurrence (n : ℕ) (hn : 0 < n) :
    fftCost (2 * n) = 2 * fftCost n + 2 * n := by
  unfold fftCost
  rw [fft_log_two_mul n hn, mul_add, mul_one, mul_assoc]

end Fourier.FastFourierTransformWanted
