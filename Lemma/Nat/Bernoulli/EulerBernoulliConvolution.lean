import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.EulerBernoulliConvolution
open scoped BigOperators
open MetaMathlibExt


/--
[euler_bernoulli_convolution](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/EulerBernoulliConvolution.lean)
-/
@[path]
private lemma euler_bernoulli_convolution_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ) * bernoulli i * bernoulli (n - i) =
    -(n : ℚ) * bernoulli (n - 1) - ((n : ℚ) - 1) * bernoulli n := by
-- proof
  apply MetaMathlibExt.euler_bernoulli_convolution n hn


-- created on 2026-10-20
