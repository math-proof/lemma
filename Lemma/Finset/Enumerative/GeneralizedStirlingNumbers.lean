import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.GeneralizedStirlingNumbers
open MetaMathlibExt


namespace MetaMathlibExt

/--
[generalizedStirlingFirst_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedStirlingNumbers.lean)
-/
@[path]
lemma generalizedStirlingFirst_eq_sum
  {n m : ℕ}
  {x : ℝ}
-- given
  (h : m ≤ n) :
-- imply
  generalizedStirlingFirst n m x =
    Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i) :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[generalizedStirlingSecond_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedStirlingNumbers.lean)
-/
@[path]
lemma generalizedStirlingSecond_eq_sum
  {n m : ℕ}
  {x : ℝ}
-- given
  (h : m ≤ n) :
-- imply
  generalizedStirlingSecond n m x =
    Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) :=
-- proof
  rfl

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
