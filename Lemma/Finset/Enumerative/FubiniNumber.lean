import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.FubiniNumber
open scoped BigOperators
open MetaMathlibExt


/--
[fubiniNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
private lemma fubiniNumber_eq_sum_eq
  {n : Nat} :
-- imply
  fubiniNumber n =
      ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * Nat.factorial k := by
-- proof
  apply MetaMathlibExt.fubiniNumber_eq_sum n

/--
[fubiniNumber_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
private lemma fubiniNumber_zero_eq
  :
-- imply
  fubiniNumber 0 = 1 := by
-- proof
  apply MetaMathlibExt.fubiniNumber_zero

/--
[fubiniNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
private lemma fubiniNumber_one_eq
  :
-- imply
  fubiniNumber 1 = 1 := by
-- proof
  apply MetaMathlibExt.fubiniNumber_one

/--
[fubiniNumber_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
private lemma fubiniNumber_two_eq
  :
-- imply
  fubiniNumber 2 = 3 := by
-- proof
  apply MetaMathlibExt.fubiniNumber_two

/--
[fubiniNumber_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
private lemma fubiniNumber_three_eq
  :
-- imply
  fubiniNumber 3 = 13 := by
-- proof
  apply MetaMathlibExt.fubiniNumber_three


-- created on 2026-10-20
