import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.AignerMotzkinInequality
open scoped BigOperators
open MetaMathlibExt


/--
[aigner_motzkin_ratio_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/AignerMotzkinInequality.lean)
-/
@[path]
private lemma aigner_motzkin_ratio_inequality_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  let M : ℕ → ℕ := by
-- proof
  apply MetaMathlibExt.aigner_motzkin_ratio_inequality n hn


-- created on 2026-10-20
