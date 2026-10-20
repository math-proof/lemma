import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.DombNumber
open scoped BigOperators
open MetaMathlibExt


/--
[dombNumber_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/DombNumber.lean)
-/
@[path]
private lemma dombNumber_unfold_eq
  {n : ℕ} :
-- imply
  dombNumber n =
    ∑ k ∈ Finset.range (n + 1),
    n.choose k ^ 2 * (2 * k).choose k * (2 * (n - k)).choose (n - k) := by
-- proof
  apply MetaMathlibExt.dombNumber_unfold n


-- created on 2026-10-20
