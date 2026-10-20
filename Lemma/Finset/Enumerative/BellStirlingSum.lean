import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.BellStirlingSum
open scoped BigOperators
open MetaMathlibExt


/--
[bell_eq_sum_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BellStirlingSum.lean)
-/
@[path]
private lemma bell_eq_sum_stirlingSecond_eq
  {n : ℕ} :
-- imply
  n.bell = ∑ k ∈ Finset.range (n + 1),
    n.stirlingSecond k := by
-- proof
  apply MetaMathlibExt.bell_eq_sum_stirlingSecond n


-- created on 2026-10-20
