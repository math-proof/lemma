import Mathlib
import sympy.Basic
import Def.Combinatorics.Enumerative.DombNumber
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[dombNumber_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DombNumber.lean)
-/
@[path]
lemma dombNumber_unfold
  {n : ℕ} :
-- imply
  dombNumber n =
    ∑ k ∈ Finset.range (n + 1),
    n.choose k ^ 2 * (2 * k).choose k * (2 * (n - k)).choose (n - k) := by
-- proof
  unfold dombNumber dombTypeSum
  simp only [pow_one]

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
