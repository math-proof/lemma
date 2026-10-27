import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[HenselianLocalRing.of_isAdicComplete_maximalIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/Henselian.lean)
-/
@[path]
lemma HenselianLocalRing.of_isAdicComplete_maximalIdeal
  [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
-- imply
  HenselianLocalRing R := by
-- proof
  have hH := IsAdicComplete.henselianRing R (IsLocalRing.maximalIdeal R)
  exact {
    is_henselian := fun f hf a0 hroot hderiv => by
      have hderiv' : IsUnit
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
          (Polynomial.eval a0 (Polynomial.derivative f))) :=
        hderiv.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R))
      exact hH.is_henselian f hf a0 hroot hderiv'
  }


-- created on 2026-10-20
-- updated on 2026-10-26
