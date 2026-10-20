import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ArithmeticFunction.TotienomialCoefficient
open MetaMathlibExt


/--
[totienomial_integral_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/TotienomialCoefficient.lean)
-/
@[path]
private lemma totienomial_integral_factorization_eq
  {n m : ℕ} :
-- imply
  ∃ N : ℕ,
    totienomialCoefficient n m = (N : ℚ) ∧
    N = ∏ p ∈ Nat.primesLE (n + m),
    ((p - 1) ^ ((n + m) / p - n / p - m / p) *
    p ^ (Nat.factorization (Nat.choose (n + m) n) p -
    ((n + m) / p - n / p - m / p))) := by
-- proof
  apply MetaMathlibExt.totienomial_integral_factorization n m


-- created on 2026-10-20
