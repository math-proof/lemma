import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BinomialHarmonicConvolution
open MetaMathlibExt


/--
[binomial_harmonic_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialHarmonicConvolution.lean)
-/
@[path]
private lemma binomial_harmonic_convolution_eq
  {k n : ℕ}
-- given
  (hk : 0 < k)
  (hkn : k ≤ n) :
-- imply
  ∑ ν ∈ Finset.Icc 1 n,
    (((Nat.choose (n + k - ν - 1) (n - 1) : ℚ) -
    (Nat.choose (n + k - ν - 1) (k - 1) : ℚ)) * harmonic ν) =
    (Nat.choose (n + k) k : ℚ) * (harmonic k - harmonic n) := by
-- proof
  apply MetaMathlibExt.binomial_harmonic_convolution k n hk hkn


-- created on 2026-10-20
