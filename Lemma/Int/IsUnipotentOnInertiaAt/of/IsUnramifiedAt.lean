import Mathlib
import sympy.Basic
import Def.GaloisRep_LocalConditions
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isUnipotentOnInertiaAt_of_isUnramifiedAt.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
  {q : ℕ}
-- given
  (h : ρ.IsUnramifiedAt q) :
-- imply
  ρ.IsUnipotentOnInertiaAt q := by
-- proof
  intro P hP σ hσ
  rw [h P hP σ hσ, LinearMap.charpoly_one, ρ.finrank_eq]


-- created on 2026-10-23
