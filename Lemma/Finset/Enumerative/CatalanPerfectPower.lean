import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CatalanPerfectPower
open MetaMathlibExt


/--
[catalan_not_perfect_power](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanPerfectPower.lean)
-/
@[path]
private lemma catalan_not_perfect_power_eq
  {n : ℕ}
-- given
  (hn : 2 ≤ n) :
-- imply
  ¬ ∃ m k : ℕ, 2 ≤ k ∧ catalan n = m ^ k := by
-- proof
  apply MetaMathlibExt.catalan_not_perfect_power n hn


-- created on 2026-10-20
