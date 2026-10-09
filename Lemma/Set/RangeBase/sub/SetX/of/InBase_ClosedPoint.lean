import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry IsLocalRing

/--
[AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_range_subset_of_isLocalRing_of_closedPoint_mem.lean)
-/
@[path]
private lemma main
  {X : Scheme.{u}}
  {U : X.Opens}
  {T : Type u} [CommRing T] [IsLocalRing T]
  {f : Spec (CommRingCat.of T) ⟶ X}
-- given
  (hx : f.base (IsLocalRing.closedPoint T) ∈ U) :
-- imply
  Set.range f.base ⊆ (U : Set ↥X) := by
-- proof
  rintro _ ⟨p, rfl⟩
  have hsp : p ⤳ IsLocalRing.closedPoint T :=
    (PrimeSpectrum.le_iff_specializes p (IsLocalRing.closedPoint T)).1 (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
  exact (hsp.map f.base.hom.continuous).mem_open U.isOpen hx


-- created on 2026-10-05
