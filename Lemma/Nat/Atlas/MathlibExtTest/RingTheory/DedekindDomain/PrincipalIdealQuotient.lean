import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[test_isPrincipal_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/PrincipalIdealQuotient.lean)
-/
@[path]
lemma test_isPrincipal_quotient
  [CommRing A]
  [IsDedekindDomain A]
  {I : Ideal A}
  {J : Ideal (A ⧸ I)}
-- given
  (hI : I ≠ ⊥) :
-- imply
  J.IsPrincipal := by
-- proof
  have := IsDedekindDomain.isPrincipalIdealRing_quotient I hI
  exact IsPrincipalIdealRing.principal J

/--
[test_isPrincipal_zmod_span_twelve](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/DedekindDomain/PrincipalIdealQuotient.lean)
-/
@[path]
lemma test_isPrincipal_zmod_span_twelve
  {J : Ideal (ℤ ⧸ Ideal.span ({12} : Set ℤ))} :
-- imply
  J.IsPrincipal := by
-- proof
  have h12 : Ideal.span ({12} : Set ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have := IsDedekindDomain.isPrincipalIdealRing_quotient _ h12
  exact IsPrincipalIdealRing.principal J
#print axioms IsDedekindDomain.isPrincipalIdealRing_quotient


-- created on 2026-10-23
