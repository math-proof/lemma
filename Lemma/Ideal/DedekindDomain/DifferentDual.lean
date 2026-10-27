import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped nonZeroDivisors


namespace Ideal

/--
[le_differentIdeal_iff_mul_dual_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentDual.lean)
-/
@[path]
lemma le_differentIdeal_iff_mul_dual_le_one
  [CommRing A] [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra K L] [Algebra A K] [Algebra A L] [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsDomain A] [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  {I : Ideal B} :
-- imply
  I ≤ differentIdeal A B ↔
    (I : FractionalIdeal B⁰ L) * FractionalIdeal.dual A K
    (1 : FractionalIdeal B⁰ L) ≤ 1 := by
-- proof
  have hdual : FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L) ≠ 0 :=
    FractionalIdeal.dual_ne_zero A K
      (@one_ne_zero (FractionalIdeal B⁰ L) _ _ _)
  rw [← FractionalIdeal.coeIdeal_le_coeIdeal L,
    coeIdeal_differentIdeal A K L B, inv_eq_one_div]
  exact FractionalIdeal.le_div_iff_mul_le hdual

end Ideal


-- created on 2026-10-20
-- updated on 2026-10-26
