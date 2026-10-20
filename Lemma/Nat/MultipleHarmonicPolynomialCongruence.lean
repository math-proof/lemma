import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleHarmonicPolynomialCongruence
open MetaMathlibExt


/--
[multiple_harmonic_polynomial_congruence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleHarmonicPolynomialCongruence.lean)
-/
@[path]
private lemma multiple_harmonic_polynomial_congruence_eq
  {n p : ℕ}
-- given
  (hn : 0 < n)
  (hp : p.Prime)
  (hpp : n + 1 < p) :
-- imply
  (∑ k ∈ Finset.Icc 1 (p - 1),
    Polynomial.C (multipleHarmonic p (k - 1) (n - 1) * (((k : ZMod p))⁻¹)) *
    (Polynomial.X : Polynomial (ZMod p)) ^ k) =
    Polynomial.C ((-1 : ZMod p) ^ (n - 1)) *
    ∑ k ∈ Finset.Icc 1 (p - 1),
    Polynomial.C (((((k : ZMod p))⁻¹) ^ n)) *
    (1 - (Polynomial.X : Polynomial (ZMod p))) ^ k := by
-- proof
  apply MetaMathlibExt.multiple_harmonic_polynomial_congruence n p hn hp hpp


-- created on 2026-10-20
