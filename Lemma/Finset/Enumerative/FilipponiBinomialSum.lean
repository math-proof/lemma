import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FilipponiBinomialSum
open scoped BigOperators
open MetaMathlibExt


/--
[filipponi_binomial_sum_formula_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
private lemma filipponi_binomial_sum_formula_general_eq
  {n h k : ℕ} :
-- imply
  let f : ℕ → ℕ → ℕ := by
-- proof
  apply MetaMathlibExt.filipponi_binomial_sum_formula_general n h k

/--
[filipponi_binomial_sum_formula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean)
-/
@[path]
private lemma filipponi_binomial_sum_formula_eq
  {n h k : ℕ}
-- given
  (hhn : h ≤ n)
  (hk : 2 * k ≤ n - h) :
-- imply
  let f : ℕ → ℕ → ℕ := by
-- proof
  apply MetaMathlibExt.filipponi_binomial_sum_formula n h k hhn hk


-- created on 2026-10-20
