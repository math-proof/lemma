/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/QuotientGroup/Basic.lean -/


import Theorem.GroupTheory.QuotientGroup.Basic
import Lemma.Nat.EqQuotientEquivRangeQuotient.of.LeKer
import Mathlib.Data.ZMod.Basic
/-!
# Tests for `QuotientGroup.quotientEquivRangeQuotient`

Usage tests for the canonical isomorphism between the quotient by a subgroup
containing a homomorphism kernel and the corresponding quotient of the range,
covering the multiplicative API, the additive API, and representative
evaluation on the concrete reduction-mod-two map.
-/


namespace QuotientEquivRangeTest

/-- Reduction mod two as an additive map. -/
def psi : ℤ →+ ZMod 2 :=
  Int.castAddHom (ZMod 2)

/-- Reduction mod two as a multiplicative map. -/
def phi : Multiplicative ℤ →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative psi

#check @QuotientGroup.quotientEquivRangeQuotient
#check @QuotientAddGroup.quotientEquivRangeQuotient
#check @QuotientGroup.quotientEquivRangeQuotient_mk
#check @QuotientAddGroup.quotientEquivRangeQuotient_mk

end QuotientEquivRangeTest
