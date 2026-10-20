import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.ArithmeticLargeSieve
open scoped BigOperators
open MathlibExt.NumberTheory.PrimeCounting


/--
[arithmeticLargeSieve_progression](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean)
-/
@[path]
private lemma arithmeticLargeSieve_progression_eq
  {N z q a : ℕ}
  {S : Finset ℕ}
-- given
  (hz : 0 < z)
  (hq : 0 < q)
  (hS : S ⊆ Finset.range N)
  (hprime : ∀ n ∈ S, (q * n + a).Prime)
  (hlarge : ∀ n ∈ S, z < q * n + a) :
-- imply
  (∑ r ∈ Finset.Icc 1 z,
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
    (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)) *
    S.card ^ 2 ≤ ((q : ℝ) / Nat.totient q) * S.card := by
-- proof
  apply MathlibExt.NumberTheory.PrimeCounting.arithmeticLargeSieve_progression N z q a hz hq S hS hprime hlarge


-- created on 2026-10-20
