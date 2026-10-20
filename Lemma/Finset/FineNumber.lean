import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.FineNumber
open MetaMathlibExt


/--
[fineNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/FineNumber.lean)
-/
@[path]
private lemma fineNumber_eq_sum_eq
  {n : Nat} :
-- imply
  fineNumber n = (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ) := by
-- proof
  apply MetaMathlibExt.fineNumber_eq_sum n


-- created on 2026-10-20
