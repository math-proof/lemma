import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.PrimeGapFactorial
open MetaMathlibExt


/--
[prime_gap_factorial_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/PrimeGapFactorial.lean)
-/
@[path]
private lemma prime_gap_factorial_general_eq
  {n p r : ℕ}
-- given
  (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
  (hp : p.Prime)
  (hlo : Nat.factorial n + 1 < p)
  (hhi : p < Nat.factorial n + r ^ 2) :
-- imply
  (p - Nat.factorial n).Prime := by
-- proof
  apply MetaMathlibExt.prime_gap_factorial_general n p r hrmin hp hlo hhi

/--
[prime_gap_factorial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/PrimeGapFactorial.lean)
-/
@[path]
private lemma prime_gap_factorial_eq
  {n p r : ℕ}
-- given
  (hr : r.Prime)
  (hrn : n < r)
  (hrmin : ∀ q : ℕ, q.Prime → n < q → r ≤ q)
  (hp : p.Prime)
  (hlo : Nat.factorial n + 1 < p)
  (hhi : p < Nat.factorial n + r ^ 2) :
-- imply
  (p - Nat.factorial n).Prime := by
-- proof
  apply MetaMathlibExt.prime_gap_factorial n p r hr hrn hrmin hp hlo hhi


-- created on 2026-10-20
