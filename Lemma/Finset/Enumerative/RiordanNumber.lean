import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RiordanNumber
open scoped BigOperators
open MetaMathlibExt


/--
[riordanNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanNumber.lean)
-/
@[path]
private lemma riordanNumber_eq_sum_eq
  {n : Nat} :
-- imply
  riordanNumber n =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : Int) ^ (n - k) * ((n.choose k : Int) * ((catalan k : Int))) := by
-- proof
  apply MetaMathlibExt.riordanNumber_eq_sum n


-- created on 2026-10-20
