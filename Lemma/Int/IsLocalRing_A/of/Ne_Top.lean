import Mathlib
import sympy.Basic


/--
[IsLocalRing_quotient_of_ne_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_quotient_of_ne_top.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {I : Ideal A}
-- given
  (hI : I ≠ ⊤) :
-- imply
  IsLocalRing (A ⧸ I) :=
-- proof
  have := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective


-- created on 2026-10-03
