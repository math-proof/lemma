import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.GarabedianGenocchiFormula
open scoped BigOperators
open MetaMathlibExt


/--
[genocchiNumber_eq_stirlingSecond_sum_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianGenocchiFormula.lean)
-/
@[path]
private lemma genocchiNumber_eq_stirlingSecond_sum_general_eq
  {n : ℕ} :
-- imply
  genocchiNumber n =
    (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
    (2 : ℚ) ^ (k - 1) := by
-- proof
  apply MetaMathlibExt.genocchiNumber_eq_stirlingSecond_sum_general n

/--
[genocchiNumber_eq_stirlingSecond_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianGenocchiFormula.lean)
-/
@[path]
private lemma genocchiNumber_eq_stirlingSecond_sum_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  genocchiNumber n =
    (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
    (2 : ℚ) ^ (k - 1) := by
-- proof
  apply MetaMathlibExt.genocchiNumber_eq_stirlingSecond_sum n hn


-- created on 2026-10-20
