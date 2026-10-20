import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MeromorphicStirlingNumber
open MetaMathlibExt


/--
[meromorphicStirlingFirst_eq_besselNumberFirst](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeromorphicStirlingNumber.lean)
-/
@[path]
private lemma meromorphicStirlingFirst_eq_besselNumberFirst_eq
  {n k : ℕ}
-- given
  (h0 : 1 ≤ k)
  (h1 : k ≤ n) :
-- imply
  meromorphicStirlingFirst n k = besselNumberFirst n k := by
-- proof
  apply MetaMathlibExt.meromorphicStirlingFirst_eq_besselNumberFirst n k h0 h1

/--
[meromorphicStirlingSecond_eq_besselNumberSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MeromorphicStirlingNumber.lean)
-/
@[path]
private lemma meromorphicStirlingSecond_eq_besselNumberSecond_eq
  {n k : ℕ}
-- given
  (h0 : n ≤ 2 * k)
  (h1 : k ≤ n) :
-- imply
  meromorphicStirlingSecond n k = besselNumberSecond n k := by
-- proof
  apply MetaMathlibExt.meromorphicStirlingSecond_eq_besselNumberSecond n k h0 h1


-- created on 2026-10-20
