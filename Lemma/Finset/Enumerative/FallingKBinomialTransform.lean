import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FallingKBinomialTransform
open scoped BigOperators
open MetaMathlibExt


/--
[binomialTransform_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FallingKBinomialTransform.lean)
-/
@[path]
private lemma binomialTransform_eq_sum_eq
  {a : ℕ → ℤ}
  {n : ℕ} :
-- imply
  binomialTransform a n =
      ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * a i := by
-- proof
  apply MetaMathlibExt.binomialTransform_eq_sum a n


-- created on 2026-10-20
