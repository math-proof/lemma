import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FussCatalanDivisibility
open MetaMathlibExt


/--
[fuss_catalan_dvd_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FussCatalanDivisibility.lean)
-/
@[path]
private lemma fuss_catalan_dvd_choose_eq
  {a n : ℕ}
-- given
  (ha : 2 ≤ a)
  (hn : 1 ≤ n) :
-- imply
  (a - 1) * n + 1 ∣ Nat.choose (a * n) n := by
-- proof
  apply MetaMathlibExt.fuss_catalan_dvd_choose a n ha hn


-- created on 2026-10-20
