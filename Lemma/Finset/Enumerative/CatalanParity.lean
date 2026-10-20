import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.CatalanParity
open MetaMathlibExt


/--
[catalan_odd_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanParity.lean)
-/
@[path]
private lemma catalan_odd_iff_eq
  {n : ℕ} :
-- imply
  Odd (catalan n) ↔ ∃ a : ℕ, n = 2 ^ a - 1 := by
-- proof
  apply MetaMathlibExt.catalan_odd_iff n


-- created on 2026-10-20
