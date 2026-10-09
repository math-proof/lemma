import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_finrank_eq_of_isPullback_of_irreducibleSpace.lean)
-/
@[path]
private lemma main
  {X Y X' Y' : Scheme.{u}} [IrreducibleSpace Y]
  {π : X ⟶ Y} [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
  {g : Y' ⟶ Y}
  {π' : X' ⟶ Y'}
  {g' : X' ⟶ X}
  {d : ℕ}
  {y : Y}
-- given
  (h : IsPullback g' π' π g)
  (h : Nonempty Y')
  (hd : ∀ y' : Y', π'.finrank y' = d) :
-- imply
  π.finrank y = d := by
-- proof
  obtain ⟨y₀⟩ := h
  have hlc := Scheme.Hom.isLocallyConstant_finrank π
  have h1 : π.finrank (g y₀) = d := by
    rw [← Scheme.Hom.finrank_of_isPullback g' π' π g h y₀]
    exact hd y₀
  rw [← h1]
  exact hlc.apply_eq_of_preconnectedSpace y (g y₀)


-- created on 2026-10-05
