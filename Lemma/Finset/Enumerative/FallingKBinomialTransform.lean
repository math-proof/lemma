import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.FallingKBinomialTransform
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[binomialTransform_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FallingKBinomialTransform.lean)
-/
@[path]
lemma binomialTransform_eq_sum
  {a : ℕ → ℤ}
  {n : ℕ} :
-- imply
  binomialTransform a n =
      ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℤ) * a i := by
-- proof
  simp [binomialTransform, fallingKBinomialTransform, one_pow, mul_one]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
