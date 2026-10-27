import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isIso_of_isFinite_of_finrank_closedPoint_eq_one.lean)
-/
@[path]
private lemma main
  (K : Type) [Field K] {Z : (Scheme : Type 1)} (p : Z ⟶ Spec (CommRingCat.of K)) [IsFinite p]
  (h : p.finrank (IsLocalRing.closedPoint K) = 1) :
  IsIso p := by
  refine (Scheme.Hom.isIso_iff_finrank_eq p).mpr ?_
  funext s
  have hs : s = IsLocalRing.closedPoint K := by
    apply PrimeSpectrum.ext
    rw [Ideal.eq_bot_of_prime s.asIdeal]
    apply (Ideal.eq_bot_of_prime _).symm
  rw [hs, h]
  rfl


-- created on 2026-10-20
