import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion
open MetaMathlibExt


/--
[rStirlingFirst_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RStirlingFirstAlternatingExpansion.lean)
-/
@[path]
private lemma rStirlingFirst_self_eq
  {m r : ℕ} :
-- imply
  rStirlingFirst r m r = if m = r then 1 else 0 := by
-- proof
  apply MetaMathlibExt.rStirlingFirst_self m r

/--
[rStirlingFirst_zero_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RStirlingFirstAlternatingExpansion.lean)
-/
@[path]
private lemma rStirlingFirst_zero_of_pos_eq
  {N r : ℕ}
-- given
  (hr : 1 ≤ r) :
-- imply
  rStirlingFirst N 0 r = 0 := by
-- proof
  apply MetaMathlibExt.rStirlingFirst_zero_of_pos N r hr

/--
[rStirlingFirst_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RStirlingFirstAlternatingExpansion.lean)
-/
@[path]
private lemma rStirlingFirst_succ_eq
  {n m r : ℕ}
-- given
  (hr : 1 ≤ r)
  (hrn : r ≤ n) :
-- imply
  rStirlingFirst (n + 1) m r =
    rStirlingFirst n (m - 1) r + n * rStirlingFirst n m r := by
-- proof
  apply MetaMathlibExt.rStirlingFirst_succ n m r hr hrn

/--
[rStirlingFirst_eq_alternating_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RStirlingFirstAlternatingExpansion.lean)
-/
@[path]
private lemma rStirlingFirst_eq_alternating_sum_eq
  {n m r : ℕ}
-- given
  (hr : 0 < r)
  (hrn : r ≤ n) :
-- imply
  (-1 : Int) ^ r * (rStirlingFirst n m r : Int) =
    Finset.sum (Finset.Icc r (n + r - m)) (fun k =>
    (Nat.stirlingFirst n (m + (k - r)) : Int) *
    (Nat.stirlingSecond (k - 1) (r - 1) : Int) * (-1 : Int) ^ k) := by
-- proof
  apply MetaMathlibExt.rStirlingFirst_eq_alternating_sum n m r hr hrn


-- created on 2026-10-20
