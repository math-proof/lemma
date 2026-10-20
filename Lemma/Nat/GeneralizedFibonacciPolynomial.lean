import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GeneralizedFibonacciPolynomial
open MetaMathlibExt


/--
[generalizedFibonacciPolynomial_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean)
-/
@[path]
private lemma generalizedFibonacciPolynomial_zero_eq
  {p0 p1 d g : Polynomial ℤ} :
-- imply
  generalizedFibonacciPolynomial p0 p1 d g 0 = p0 := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciPolynomial_zero p0 p1 d g

/--
[generalizedFibonacciPolynomial_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean)
-/
@[path]
private lemma generalizedFibonacciPolynomial_one_eq
  {p0 p1 d g : Polynomial ℤ} :
-- imply
  generalizedFibonacciPolynomial p0 p1 d g 1 = p1 := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciPolynomial_one p0 p1 d g

/--
[generalizedFibonacciPolynomial_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFibonacciPolynomial.lean)
-/
@[path]
private lemma generalizedFibonacciPolynomial_add_two_eq
  {p0 p1 d g : Polynomial ℤ}
  {n : ℕ} :
-- imply
  generalizedFibonacciPolynomial p0 p1 d g (n + 2) =
      d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
        g * generalizedFibonacciPolynomial p0 p1 d g n := by
-- proof
  apply MetaMathlibExt.generalizedFibonacciPolynomial_add_two p0 p1 d g n


-- created on 2026-10-20
