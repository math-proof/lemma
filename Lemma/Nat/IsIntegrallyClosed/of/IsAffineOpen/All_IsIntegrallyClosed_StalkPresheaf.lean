import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
[AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean)
-/

private lemma  isIntegrallyClosed_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {_} _ => ⟨0, Subsingleton.elim _ _⟩
@[main]
private lemma main
  {X : Scheme.{u}} [IsIntegral X]
  {U : X.Opens}
-- given
  (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
  (hU : IsAffineOpen U) :
-- imply
  IsIntegrallyClosed Γ(X, U) := by
-- proof
  by_cases hne : Nonempty U
  ·
    haveI := hne
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : U, hU.primeIdealOf x = y :=
      ⟨⟨hU.fromSpec.base y, hy⟩, hU.fromSpec.injective (by rw [hU.fromSpec_primeIdealOf])⟩
    haveI : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := by
      have := hU.isLocalization_stalk x
      rw [hx] at this
      exact this
    haveI := h x.1
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv
  ·
    have hU0 : U = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hne ⟨⟨z, hz⟩⟩
    subst hU0
    exact isIntegrallyClosed_of_subsingleton _


-- created on 2026-10-05
