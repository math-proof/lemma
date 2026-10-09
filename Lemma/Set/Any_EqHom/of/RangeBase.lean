import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsClosedImmersion_exists_iso_hom_comp_eq_of_range_eq.lean)
-/
@[path]
private lemma main
  {A B X : Scheme.{u}} [IsReduced A] [IsReduced B]
  {f : A ⟶ X} [IsClosedImmersion f]
  {g : B ⟶ X} [IsClosedImmersion g]
-- given
  (h : Set.range f.base = Set.range g.base) :
-- imply
  ∃ e : A ≅ B, e.hom ≫ g = f := by
-- proof
  have : Surjective (pullback.fst f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_fst, ← h, Set.preimage_range]⟩
  have : Surjective (pullback.snd f g) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, h, Set.preimage_range]⟩
  have : IsIso (pullback.fst f g) := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso (pullback.snd f g) := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨(asIso (pullback.fst f g)).symm ≪≫ asIso (pullback.snd f g), ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc]
  rw [IsIso.inv_comp_eq, pullback.condition]


-- created on 2026-10-05
