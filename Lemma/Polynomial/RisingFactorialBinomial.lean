import Mathlib
import sympy.Basic
import sympy.Algebra.Polynomial.RisingFactorialBinomial

open MetaMathlibExt
open scoped BigOperators

/--
[ascPochhammer_eval_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Polynomial/RisingFactorialBinomial.lean)
-/
@[path]
private lemma ascPochhammer_eval_add_eq
-- given
  (n : ℕ) (a b : ℝ) :
-- imply
  (ascPochhammer ℝ n).eval (a + b) =
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
      (ascPochhammer ℝ k).eval a *
      (ascPochhammer ℝ (n - k)).eval b := by
-- proof
  apply ascPochhammer_eval_add


-- created on 2026-10-09
