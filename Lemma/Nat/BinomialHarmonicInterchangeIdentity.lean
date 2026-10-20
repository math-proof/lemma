import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BinomialHarmonicInterchangeIdentity
open MetaMathlibExt


/--
[binomial_harmonic_interchange_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BinomialHarmonicInterchangeIdentity.lean)
-/
@[path]
private lemma binomial_harmonic_interchange_identity_eq
  [Field K] [CharZero K]
  {n : ℕ}
  {a : ℕ → K} :
-- imply
  Finset.sum (Finset.Icc 1 n)
    (fun k => (1 / (k : K)) *
    Finset.sum (Finset.Icc 1 k) (fun j => (Nat.choose k j : K) * a j)) =
    Finset.sum (Finset.Icc 1 n) (fun k => (Nat.choose n k : K) * a k / (k : K)) := by
-- proof
  apply MetaMathlibExt.binomial_harmonic_interchange_identity n a


-- created on 2026-10-20
