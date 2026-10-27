/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
open scoped BigOperators


namespace Fourier.FastFourierTransformWanted

/-!
# Fast Fourier transform

The radix-2 Cooley–Tukey splitting identity (correctness core of the FFT) and
the operation-count recurrence with its `n log n` closed form (complexity
skeleton).

Sources: `undergrad.yaml`, section "Fourier transform", entry "fast Fourier
transform" (empty); J. W. Cooley and J. W. Tukey, An algorithm for the machine
calculation of complex Fourier series, Math. Comp. 19 (1965), 297–301.
-/

/-- The unnormalized discrete Fourier sum of length `N` at frequency `k`. -/
def dftSum (N : ℕ) (ω : ℂ) (f : ℕ → ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, ω ^ (j * k) * f j

end Fourier.FastFourierTransformWanted
