import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.RiordanNumber
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[riordanNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RiordanNumber.lean)
-/
@[path]
lemma riordanNumber_eq_sum
  {n : Nat} :
-- imply
  riordanNumber n =
      ∑ k ∈ Finset.range (n + 1),
        (-1 : Int) ^ (n - k) * ((n.choose k : Int) * ((catalan k : Int))) :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
