import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.ClassGroup.CoprimeRepresentative
open Ideal


/--
[Ideal.exists_isCoprime_mul_isPrincipal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ClassGroup/CoprimeRepresentative.lean)
-/
@[path]
private lemma Ideal_exists_isCoprime_mul_isPrincipal_eq
  [CommRing A] [IsDedekindDomain A]
  {I a : Ideal A}
-- given
  (hI : I ≠ ⊥)
  (ha : a ≠ ⊥) :
-- imply
  ∃ J : Ideal A, IsCoprime J a ∧ Submodule.IsPrincipal (I * J) := by
-- proof
  apply Ideal.exists_isCoprime_mul_isPrincipal I a hI ha

/--
[ClassGroup.exists_mk0_eq_and_isCoprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ClassGroup/CoprimeRepresentative.lean)
-/
@[path]
private lemma ClassGroup_exists_mk0_eq_and_isCoprime_eq
  [CommRing A] [IsDedekindDomain A]
  {c : ClassGroup A}
  {a : Ideal A}
-- given
  (ha : a ≠ ⊥) :
-- imply
  ∃ (K : Ideal A) (hK : K ≠ ⊥),
      ClassGroup.mk0 ⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr hK⟩ = c ∧
        IsCoprime K a := by
-- proof
  apply ClassGroup.exists_mk0_eq_and_isCoprime c a ha


-- created on 2026-10-20
