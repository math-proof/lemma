import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.EngelBellLogConvexity
open MetaMathlibExt


/--
[engel_bell_log_convexity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/EngelBellLogConvexity.lean)
-/
@[path]
private lemma engel_bell_log_convexity_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  (Nat.bell n) ^ 2 ≤ Nat.bell (n - 1) * Nat.bell (n + 1) := by
-- proof
  apply MetaMathlibExt.engel_bell_log_convexity n hn


-- created on 2026-10-20
