import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_eq_univ_of_isClopen_of_range_specMap_subset_of_injective.lean)
-/
@[main]
private lemma main
  {R₀ L : Type} [CommRing R₀] [CommRing L]
  {φ : R₀ →+* L}
  {W : Set ↥(Spec (CommRingCat.of R₀))}
-- given
  (hφ : Function.Injective φ)
  (hW : IsClopen W)
  (hWL : Set.range (Spec.map (CommRingCat.ofHom φ)).base ⊆ W) :
-- imply
  W = Set.univ := by
-- proof
  have hdense : DenseRange (Spec.map (CommRingCat.ofHom φ)).base :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).2
      (by rw [(RingHom.injective_iff_ker_eq_bot φ).1 hφ]; exact bot_le)
  apply Set.eq_univ_of_univ_subset
  rw [← hdense.closure_range]
  exact (hW.1.closure_subset_iff).2 hWL


-- created on 2026-10-05
