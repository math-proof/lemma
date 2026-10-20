import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.AbelBernoulliSums
open Finset Nat Polynomial
open MetaMathlibExt


/--
[abel_bernoulli_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/AbelBernoulliSums.lean)
-/
@[path]
private lemma abel_bernoulli_sum_eq
  :
-- imply
  ∀ (n : ℕ) (x y : ℂ), x ≠ 0 →
    ∑ l ∈ Finset.range (n + 1),
    (Nat.choose n l : ℂ) * (x + (l : ℂ)) ^ ((l : ℤ) - 1) *
    Polynomial.eval₂ (algebraMap ℚ ℂ) (y + (n - l : ℕ))
    (Polynomial.bernoulli (n - l)) =
    (1 / x) * Polynomial.eval₂ (algebraMap ℚ ℂ) (y + x + (n : ℂ))
    (Polynomial.bernoulli n) := by
-- proof
  apply MetaMathlibExt.abel_bernoulli_sum


-- created on 2026-10-20
