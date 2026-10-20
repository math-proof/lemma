import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BAryBinomialGeneratingFunction
open MetaMathlibExt


/--
[bAryBinomialCoefficient_generating_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialGeneratingFunction.lean)
-/
@[path]
private lemma bAryBinomialCoefficient_generating_function_eq
  [CommSemiring R]
  {b n : ℕ}
  {x : R}
-- given
  (hb : 2 ≤ b) :
-- imply
  ∑ k ∈ Finset.range (n + 1), (bAryBinomialCoefficient b n k hb : R) * x ^ k =
    ∏ l ∈ Finset.range (Nat.digits b n).length,
    (1 + x ^ (b ^ l)) ^ ((Nat.digits b n).getD l 0) := by
-- proof
  apply MetaMathlibExt.bAryBinomialCoefficient_generating_function b n x hb

/--
[base_digits_binomial_generating_function](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BAryBinomialGeneratingFunction.lean)
-/
@[path]
private lemma base_digits_binomial_generating_function_eq
  [CommRing R]
  {b n : ℕ}
  {x : R}
-- given
  (hb : 2 ≤ b) :
-- imply
  ∑ k ∈ Finset.range (n + 1),
    (∏ l ∈ Finset.range (Nat.digits b n).length,
    (((Nat.digits b n).getD l 0).choose ((Nat.digits b k).getD l 0) : R)) * x ^ k =
    ∏ l ∈ Finset.range (Nat.digits b n).length,
    (1 + x ^ (b ^ l)) ^ ((Nat.digits b n).getD l 0) := by
-- proof
  apply MetaMathlibExt.base_digits_binomial_generating_function b n x hb


-- created on 2026-10-20
