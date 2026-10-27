/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Theorem.Analysis.Fourier.FastFourierTransform
open scoped BigOperators


namespace Fourier.FastFourierTransformWanted

/-- Closed-form FFT operation count: `n * log 2 n`. -/
def fftCost (n : ℕ) : ℕ :=
  n * Nat.log 2 n

end Fourier.FastFourierTransformWanted
