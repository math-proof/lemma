/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/QuotientGroup/Basic.lean -/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.GroupTheory.QuotientGroup.Basic
/-!
# Quotients by subgroups containing a homomorphism kernel

This module provides the canonical isomorphism between the quotient of a
commutative group by a subgroup containing a homomorphism kernel and the
corresponding quotient of the homomorphism range.

## Main results

* `QuotientGroup.quotientEquivRangeQuotient`: for `f : A →* C` and
  `B : Subgroup A` with `f.ker ≤ B`, the canonical isomorphism
  `A ⧸ B ≃* f.range ⧸ (B.map f).subgroupOf f.range`.
* `QuotientGroup.quotientEquivRangeQuotient_mk`: evaluation on representatives.
-/


namespace QuotientGroup

/-- Evaluation of `QuotientGroup.quotientEquivRangeQuotient` on representatives. -/
@[to_additive (attr := simp)
/-- Evaluation of `QuotientAddGroup.quotientEquivRangeQuotient` on representatives. -/]
theorem quotientEquivRangeQuotient_mk
    {A C : Type*} [CommGroup A] [CommGroup C]
    (f : A →* C) (B : Subgroup A) (hB : f.ker ≤ B) (a : A) :
    quotientEquivRangeQuotient f B hB (QuotientGroup.mk a) =
      QuotientGroup.mk (f.rangeRestrict a) :=
  rfl

end QuotientGroup
