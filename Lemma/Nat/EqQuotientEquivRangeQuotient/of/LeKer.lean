import Mathlib
import sympy.Basic
import Theorem.GroupTheory.QuotientGroup.Basic
open QuotientGroup


namespace Definitions
end Definitions
/--
[quotientEquivRangeQuotient_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/QuotientGroup/Basic.lean)
-/
@[path]
private lemma quotientEquivRangeQuotient_mk_eq
  [CommGroup A] [CommGroup C]
  {f : A →* C}
  {B : Subgroup A}
  {a : A}
-- given
  (hB : f.ker ≤ B) :
-- imply
  quotientEquivRangeQuotient f B hB (QuotientGroup.mk a) =
      QuotientGroup.mk (f.rangeRestrict a) := by
-- proof
  apply QuotientGroup.quotientEquivRangeQuotient_mk f B hB a


-- created on 2026-10-20
-- updated on 2026-10-24
