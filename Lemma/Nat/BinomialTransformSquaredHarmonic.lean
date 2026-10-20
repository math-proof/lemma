import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BinomialTransformSquaredHarmonic
open MetaMathlibExt


/--
[binomial_transform_sq_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialTransformSquaredHarmonic.lean)
-/
@[path]
private lemma binomial_transform_sq_harmonic_eq
  {s : ℂ}
  {n : ℕ}
-- given
  (hs : ∀ m : ℕ, s ≠ -((m : ℂ) + 1))
  (hn : 0 < n) :
-- imply
  ∑ k ∈ Finset.Icc 1 n,
    ((-1 : ℂ) ^ k * ((descPochhammer ℂ k).eval (s + (n : ℂ)) / (k.factorial : ℂ)) *
    (harmonic k : ℂ) ^ 2) =
    (-1 : ℂ) ^ n * ((descPochhammer ℂ n).eval (s + (n : ℂ) - 1) / (n.factorial : ℂ)) *
    ((harmonic n : ℂ) ^ 2 + 2 * (harmonic n : ℂ) / (s + (n : ℂ)) +
    2 / (s + (n : ℂ)) ^ 2) +
    (harmonic n : ℂ) / (s + (n : ℂ)) - 2 / (s + (n : ℂ)) ^ 2 -
    s / (s + (n : ℂ)) *
    ∑ k ∈ Finset.Icc 1 n,
    (((-1 : ℂ) ^ k * ((descPochhammer ℂ (k - 1)).eval (s + (k : ℂ) - 1) /
    ((k - 1).factorial : ℂ))) / ((k : ℂ) ^ 2 * (Nat.choose n k : ℂ))) := by
-- proof
  apply MetaMathlibExt.binomial_transform_sq_harmonic s n hs hn


-- created on 2026-10-20
