import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalHom_algebraMap_quotient_of_ne_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalHom_algebraMap_quotient_of_ne_top.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
  {I : Ideal A}
-- given
  (hI : I ≠ ⊤) :
-- imply
  IsLocalHom (algebraMap 𝒪 (A ⧸ I)) := by
-- proof
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  rw [← Ideal.Quotient.mk_comp_algebraMap]
  exact RingHom.isLocalHom_comp _ _


-- created on 2026-10-03
