import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.RelativelyPrimeSubsetCounts
open MetaMathlibExt


/--
[mobius_formula_relatively_prime_subset_counts_interval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/RelativelyPrimeSubsetCounts.lean)
-/
@[path]
private lemma mobius_formula_relatively_prime_subset_counts_interval_eq
  {ℓ m k : ℕ}
-- given
  (h_lt : ℓ < m)
  (h_k : 1 ≤ k) :
-- imply
  (((Finset.powerset (Finset.Ioc ℓ m)).filter
    (fun H => H.Nonempty ∧ Finset.gcd H id = 1)).card : ℤ) =
    ∑ d ∈ Finset.Icc 1 m,
    ArithmeticFunction.moebius d * ((2 : ℤ) ^ (m / d - ℓ / d) - 1) ∧
    (((Finset.powerset (Finset.Ioc ℓ m)).filter
    (fun H => H.card = k ∧ Finset.gcd H id = 1)).card : ℤ) =
    ∑ d ∈ Finset.Icc 1 m,
    ArithmeticFunction.moebius d * (Nat.choose (m / d - ℓ / d) k : ℤ) := by
-- proof
  apply MetaMathlibExt.mobius_formula_relatively_prime_subset_counts_interval ℓ m k h_lt h_k


-- created on 2026-10-20
