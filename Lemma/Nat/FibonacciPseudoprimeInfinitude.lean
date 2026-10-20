import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.FibonacciPseudoprimeInfinitude
open MetaMathlibExt


/--
[infinitely_many_primes_fibonacci_pseudoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FibonacciPseudoprimeInfinitude.lean)
-/
@[path]
private lemma infinitely_many_primes_fibonacci_pseudoprime_eq
  :
-- imply
  Set.Infinite {p : ℕ | p.Prime ∧
    let n := by
-- proof
  apply MetaMathlibExt.infinitely_many_primes_fibonacci_pseudoprime


-- created on 2026-10-20
