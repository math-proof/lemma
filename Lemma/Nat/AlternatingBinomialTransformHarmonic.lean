import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.AlternatingBinomialTransformHarmonic
open Work
open Work Work2
open Work Work2 Work3 Work4
open Work3
open Work3 Work4 Work6
open MetaMathlibExt


/--
[alternating_binomial_transform_harmonic_numbers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/AlternatingBinomialTransformHarmonic.lean)
-/
@[path]
private lemma alternating_binomial_transform_harmonic_numbers_eq
  {s : ℂ}
  {n : ℕ}
-- given
  (hs : ∀ m : ℕ, s ≠ -((m + 1 : ℕ) : ℂ))
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.Icc 1 n,
    ((-1 : ℂ) ^ k *
    (Complex.Gamma (((n : ℂ) + s) + 1) /
    (Complex.Gamma ((k : ℂ) + 1) * Complex.Gamma (((n : ℂ) + s) - (k : ℂ) + 1))) *
    ((harmonic k : ℚ) : ℂ)) =
    (-1 : ℂ) ^ n *
    (Complex.Gamma ((s + (n : ℂ) - 1) + 1) /
    (Complex.Gamma ((n : ℂ) + 1) *
    Complex.Gamma ((s + (n : ℂ) - 1) - (n : ℂ) + 1))) *
    ((harmonic n : ℚ) : ℂ) +
    ((-1 : ℂ) ^ n / (s + (n : ℂ))) *
    (Complex.Gamma ((s + (n : ℂ) - 1) + 1) /
    (Complex.Gamma ((n : ℂ) + 1) *
    Complex.Gamma ((s + (n : ℂ) - 1) - (n : ℂ) + 1))) -
    1 / (s + (n : ℂ)) := by
-- proof
  apply MetaMathlibExt.alternating_binomial_transform_harmonic_numbers s n hs hn


-- created on 2026-10-20
