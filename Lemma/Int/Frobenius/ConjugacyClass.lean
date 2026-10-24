import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.Frobenius.ConjugacyClass


/--
[arithFrobConjClass_mem_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/ConjugacyClass.lean)
-/
@[path]
lemma arithFrobConjClass_mem_carrier
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Finite G] [Algebra.IsInvariant R S G]
  {Q : Ideal S} [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] :
-- imply
  arithFrobAt R G Q ∈ (arithFrobConjClass (R :=
-- proof
  ConjClasses.mem_carrier_mk

/--
[arithFrobConjClass_eq_of_under_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Frobenius/ConjugacyClass.lean)
-/
@[path]
lemma arithFrobConjClass_eq_of_under_eq
  [CommRing R] [CommRing S] [Algebra R S] [Group G] [MulSemiringAction G S] [SMulCommClass G R S] [Finite G] [Algebra.IsInvariant R S G]
  {Q Q' : Ideal S} [Q.IsPrime] [Finite (S ⧸ Q)] [Algebra.IsUnramifiedAt R Q] [Q'.IsPrime] [Finite (S ⧸ Q')] [Algebra.IsUnramifiedAt R Q']
-- given
  (h : Q.under R = Q'.under R) :
-- imply
  arithFrobConjClass (R := by
-- proof
  unfold arithFrobConjClass
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  exact isConj_arithFrobAt R G Q Q' h


-- created on 2026-10-20
-- updated on 2026-10-23
