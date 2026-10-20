import Mathlib
import sympy.Basic
import sympy.atlas.InformationTheory.LogSum
open Finset
open Real


/--
[sum_mul_log_sum_div_sum_le_sum_mul_log_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/InformationTheory/LogSum.lean)
-/
@[path]
private lemma sum_mul_log_sum_div_sum_le_sum_mul_log_div_eq
  {s : Finset ι}
  {p q : ι → ℝ}
-- given
  (hp : ∀ i ∈ s, 0 ≤ p i)
  (hq : ∀ i ∈ s, 0 < q i) :
-- imply
  (∑ i ∈ s, p i) * log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i)
    ≤ ∑ i ∈ s, p i * log (p i / q i) := by
-- proof
  apply Real.sum_mul_log_sum_div_sum_le_sum_mul_log_div s p q hp hq


-- created on 2026-10-20
