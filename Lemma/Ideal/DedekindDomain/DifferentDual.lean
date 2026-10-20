import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.DifferentDual
open scoped nonZeroDivisors
open Ideal


/--
[le_differentIdeal_iff_mul_dual_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/DifferentDual.lean)
-/
@[path]
private lemma le_differentIdeal_iff_mul_dual_le_one_eq
  [CommRing A] [CommRing B] [Field K] [Field L] [Algebra A B] [Algebra K L] [Algebra A K] [Algebra A L] [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsDomain A] [IsFractionRing A K] [IsFractionRing B L] [FiniteDimensional K L] [Algebra.IsSeparable K L] [IsIntegralClosure B A L] [IsIntegrallyClosed A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  {I : Ideal B} :
-- imply
  I ≤ differentIdeal A B ↔
      (I : FractionalIdeal B⁰ L) * FractionalIdeal.dual A K
          (1 : FractionalIdeal B⁰ L) ≤ 1 := by
-- proof
  apply Ideal.le_differentIdeal_iff_mul_dual_le_one A K L B I


-- created on 2026-10-20
