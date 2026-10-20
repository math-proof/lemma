import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Bernoulli.CarlitzIdentity
open Nat Finset
open MetaMathlibExt


/--
[carlitz_bernoulli_sum_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/CarlitzIdentity.lean)
-/
@[path]
private lemma carlitz_bernoulli_sum_symm_eq
  {m n : ℕ} :
-- imply
  (-1 : ℚ) ^ m * (Finset.range (m + 1)).sum
    (fun k => (Nat.choose m k : ℚ) * bernoulli (n + k)) =
    (-1 : ℚ) ^ n * (Finset.range (n + 1)).sum
    (fun k => (Nat.choose n k : ℚ) * bernoulli (m + k)) := by
-- proof
  apply MetaMathlibExt.carlitz_bernoulli_sum_symm m n


-- created on 2026-10-20
