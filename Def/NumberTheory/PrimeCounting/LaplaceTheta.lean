/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/LaplaceTheta.lean -/

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.Chebyshev
import Lemma.Real.LaplaceTransform.ExponentialBound
open MeasureTheory Finset

/-!
# Laplace transform of `theta (exp ·)`

ATLAS NumberTheoryI Lemma 16.10: for `1 < s.re`, the Laplace transform of
`theta (exp t)` equals `primeLogSeries s / s` and is holomorphic on
`{s | 1 < s.re}`.
-/


namespace Chebyshev

/-- Prime log series `∑' p, log p * p ^ (-s)`, the numerator of Lemma 16.10. -/
noncomputable def primeLogSeries (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)

end Chebyshev
