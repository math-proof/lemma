/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Theorem.Analysis.Fourier.FastFourierTransform

@[expose] public section

open scoped BigOperators


namespace Fourier.FastFourierTransformWanted

/-- Closed-form FFT operation count: `n * log 2 n`. -/
def fftCost (n : ℕ) : ℕ :=
  n * Nat.log 2 n

end Fourier.FastFourierTransformWanted
