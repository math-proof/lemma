import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.KanekoBernoulliStirling
open MetaMathlibExt


/--
[kaneko_bernoulli_stirling_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/KanekoBernoulliStirling.lean)
-/
@[path]
private lemma kaneko_bernoulli_stirling_sum_eq
  {n : ℕ} :
-- imply
  bernoulli n = ∑ m ∈ Finset.Icc 1 (n + 1),
    (-1 : ℚ) ^ (m - 1) * (Nat.factorial (m - 1) : ℚ) *
    (Nat.stirlingSecond n (m - 1) : ℚ) / (m : ℚ) := by
-- proof
  apply MetaMathlibExt.kaneko_bernoulli_stirling_sum n


-- created on 2026-10-20
