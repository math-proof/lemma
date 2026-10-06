import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field.lean)
-/
@[main]
private lemma main
  [Field k₀] [CommRing Bb] [Nontrivial Bb]
  {ψ : k₀ →+* Bb}
  {T : Scheme.{0}}
  {t : T ⟶ Spec (CommRingCat.of k₀)} :
-- imply
  (pullback.fst t (Spec.map (CommRingCat.ofHom ψ))).ker = ⊥ := by
-- proof
  haveI : IsDominant (Spec.map (CommRingCat.ofHom ψ)) := by
    rw [isDominant_iff]
    have hr : Set.range (Spec.map (CommRingCat.ofHom ψ)).base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y⟩ := (inferInstance : Nonempty (PrimeSpectrum Bb))
      exact ⟨y, Subsingleton.elim _ _⟩
    rw [DenseRange, hr]
    exact dense_univ
  haveI : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom ψ)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : Flat t := inferInstance
  exact (pullback.fst t (Spec.map (CommRingCat.ofHom ψ))).ker_eq_bot


-- created on 2026-10-05
