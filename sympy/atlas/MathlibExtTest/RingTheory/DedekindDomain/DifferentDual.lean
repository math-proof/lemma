/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/DifferentDual.lean -/


import Lemma.Ideal.DedekindDomain.DifferentDual

open scoped nonZeroDivisors

variable (A K L B : Type*)
variable [CommRing A] [CommRing B] [Field K] [Field L]
variable [Algebra A B] [Algebra K L] [Algebra A K] [Algebra A L]
variable [Algebra B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]
variable [IsDomain A] [IsFractionRing A K] [IsFractionRing B L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [IsIntegralClosure B A L] [IsIntegrallyClosed A]
variable [IsDedekindDomain B] [Module.IsTorsionFree A B]

example (I : Ideal B) :
    I ≤ differentIdeal A B ↔
      (I : FractionalIdeal B⁰ L) * FractionalIdeal.dual A K
        (1 : FractionalIdeal B⁰ L) ≤ 1 :=
  Ideal.le_differentIdeal_iff_mul_dual_le_one A K L B I

example (I : Ideal B) (h : I ≤ differentIdeal A B) :
    (I : FractionalIdeal B⁰ L) * FractionalIdeal.dual A K
      (1 : FractionalIdeal B⁰ L) ≤ 1 :=
  (Ideal.le_differentIdeal_iff_mul_dual_le_one A K L B I).mp h

example (I : Ideal B)
    (h : (I : FractionalIdeal B⁰ L) * FractionalIdeal.dual A K
      (1 : FractionalIdeal B⁰ L) ≤ 1) :
    I ≤ differentIdeal A B :=
  (Ideal.le_differentIdeal_iff_mul_dual_le_one A K L B I).mpr h
