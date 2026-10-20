import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.StirlingSecondExplicit
open scoped BigOperators
open MetaMathlibExt


/--
[stirlingSecond_mul_factorial_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma stirlingSecond_mul_factorial_eq_sum_eq
  {t k : ℕ} :
-- imply
  (Nat.stirlingSecond t k : ℝ) * (k.factorial : ℝ) =
    ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ (k - j) * (Nat.choose k j : ℝ) * (j : ℝ) ^ t := by
-- proof
  apply MetaMathlibExt.stirlingSecond_mul_factorial_eq_sum t k

/--
[hasSum_stirlingSecond_succ_egf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/StirlingSecondExplicit.lean)
-/
@[path]
private lemma hasSum_stirlingSecond_succ_egf_eq
  {j : ℕ}
  {x : ℝ} :
-- imply
  HasSum
    (fun n : ℕ =>
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (x ^ n / n.factorial))
    (Real.exp x * (Real.exp x - 1) ^ j / j.factorial) := by
-- proof
  apply MetaMathlibExt.hasSum_stirlingSecond_succ_egf j x


-- created on 2026-10-20
