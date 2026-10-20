import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DedekindDomain.PrincipalIdealQuotient


/--
[IsDedekindDomain.isPrincipalIdealRing_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DedekindDomain/PrincipalIdealQuotient.lean)
-/
@[path]
private lemma IsDedekindDomain_isPrincipalIdealRing_quotient_eq
  [CommRing A] [IsDedekindDomain A]
  {I : Ideal A}
-- given
  (hI : I ≠ ⊥) :
-- imply
  IsPrincipalIdealRing (A ⧸ I) where
  principal J := by
-- proof
  apply IsDedekindDomain.isPrincipalIdealRing_quotient I hI


-- created on 2026-10-20
