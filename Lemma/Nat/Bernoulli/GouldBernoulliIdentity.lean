import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.GouldBernoulliIdentity
open scoped BigOperators
open MetaMathlibExt


/--
[gould_bernoulli_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/GouldBernoulliIdentity.lean)
-/
@[path]
private lemma gould_bernoulli_identity_eq
  {n : ℕ}
  {x : ℚ} :
-- imply
  ∑ k ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ k * (Nat.choose n k : ℚ) *
    (Polynomial.bernoulli (n + 1)).eval (x - k) =
    (Nat.factorial (n + 1) : ℚ) / 2 * (2 * x - n - 1) := by
-- proof
  apply MetaMathlibExt.gould_bernoulli_identity n x


-- created on 2026-10-20
