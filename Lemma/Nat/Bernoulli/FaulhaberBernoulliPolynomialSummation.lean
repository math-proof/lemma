import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.FaulhaberBernoulliPolynomialSummation
open MetaMathlibExt


/--
[faulhaber_bernoulli_polynomial_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/FaulhaberBernoulliPolynomialSummation.lean)
-/
@[path]
private lemma faulhaber_bernoulli_polynomial_sum_eq
  {k n : ℕ} :
-- imply
  Finset.sum (Finset.range n) (fun j =>
    (Polynomial.bernoulli k).comp (Polynomial.X + Polynomial.C ((j : ℚ) + 1))) =
    Polynomial.C (1 / ((k : ℚ) + 1)) * Finset.sum (Finset.range (k + 1)) (fun r =>
    Polynomial.C ((Nat.choose (k + 1) (r + 1) : ℚ) *
    ((Polynomial.bernoulli (r + 1)).eval ((n : ℚ) + 1) +
    (-1 : ℚ) ^ r * _root_.bernoulli (r + 1))) *
    Polynomial.bernoulli (k - r)) := by
-- proof
  apply MetaMathlibExt.faulhaber_bernoulli_polynomial_sum k n


-- created on 2026-10-20
