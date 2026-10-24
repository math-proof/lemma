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


-- created on 2026-10-10
-- updated on 2026-10-24
