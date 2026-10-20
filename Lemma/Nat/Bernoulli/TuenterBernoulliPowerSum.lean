import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.TuenterBernoulliPowerSum
open scoped BigOperators
open MetaMathlibExt


/--
[tuenter_bernoulli_power_sum_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/TuenterBernoulliPowerSum.lean)
-/
@[path]
private lemma tuenter_bernoulli_power_sum_identity_eq
  {a b : ℂ}
  {n : ℕ}
  {sigma : ℂ → ℕ → ℂ}
-- given
  (hn : 0 < n)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hsigma : ∀ x i, ((i + 1 : ℕ) : ℂ) * sigma x i = (Polynomial.bernoulli (i + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) - (bernoulli (i + 1) : ℂ))
  (hden : b ^ n - a ^ n ≠ 0) :
-- imply
  (bernoulli n : ℂ) =
    1 / (b ^ n - a ^ n) *
    ∑ i ∈ Finset.Icc 1 n,
    (n.choose i : ℂ) * (bernoulli (n - i) : ℂ) *
    (a ^ ((n : ℤ) - 1 - (i : ℤ)) * b ^ i * sigma (a - 1) i -
    a ^ i * b ^ ((n : ℤ) - 1 - (i : ℤ)) * sigma (b - 1) i) := by
-- proof
  apply MetaMathlibExt.tuenter_bernoulli_power_sum_identity a b n hn ha hb sigma hsigma hden


-- created on 2026-10-20
