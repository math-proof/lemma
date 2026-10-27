import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.FubiniNumber
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[fubiniNumber_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
lemma fubiniNumber_eq_sum
  {n : Nat} :
-- imply
  fubiniNumber n =
      ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * Nat.factorial k :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fubiniNumber_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
lemma fubiniNumber_zero
  :
-- imply
  fubiniNumber 0 = 1 := by
-- proof
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fubiniNumber_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
lemma fubiniNumber_one
  :
-- imply
  fubiniNumber 1 = 1 := by
-- proof
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fubiniNumber_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
lemma fubiniNumber_two
  :
-- imply
  fubiniNumber 2 = 3 := by
-- proof
decide

end MetaMathlibExt

namespace MetaMathlibExt

/--
[fubiniNumber_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FubiniNumber.lean)
-/
@[path]
lemma fubiniNumber_three
  :
-- imply
  fubiniNumber 3 = 13 := by
-- proof
decide

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
