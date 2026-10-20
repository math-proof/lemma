import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.FibonacciPrimeDivisibility
open MetaMathlibExt


/--
[fib_prime_dvd_fib_of_legendre_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FibonacciPrimeDivisibility.lean)
-/
@[path]
private lemma fib_prime_dvd_fib_of_legendre_sub_eq
  {p : ℕ} [Fact (Nat.Prime p)]
-- given
  (h0 : p ≠ 5)
  (h1 : 2 < p) :
-- imply
  p ∣ Nat.fib (if legendreSym p 5 = 1 then p - 1 else p + 1) := by
-- proof
  apply MetaMathlibExt.fib_prime_dvd_fib_of_legendre_sub p h0 h1


-- created on 2026-10-20
