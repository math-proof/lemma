import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale.lean)
-/
@[main]
private lemma main
  {Z X Y : Scheme.{u}}
  {i : Z ⟶ X} [IsClosedImmersion i]
  {g : X ⟶ Y} [Etale g] [Flat (i ≫ g)] [LocallyOfFinitePresentation (i ≫ g)] :
-- imply
  IsOpenImmersion i ∧ Etale (i ≫ g) := by
-- proof
  have hmono : Mono i := inferInstance
  have hdiag : IsOpenImmersion (Limits.pullback.diagonal i) := inferInstance
  have hi : FormallyUnramified i := inferInstance
  have hg : FormallyUnramified g := inferInstance
  have hig : FormallyUnramified (i ≫ g) := MorphismProperty.comp_mem _ i g hi hg
  have het : Etale (i ≫ g) := Etale.of_formallyUnramified_of_flat (f := i ≫ g)
  have heti : Etale i := Etale.of_comp i g
  have hflat : Flat i := (Etale.iff_flat_and_formallyUnramified.mp heti).1
  have hlfp : LocallyOfFinitePresentation i := (Etale.iff_flat_and_formallyUnramified.mp heti).2.2
  exact ⟨IsOpenImmersion.of_flat_of_mono i, het⟩


-- created on 2026-10-05
