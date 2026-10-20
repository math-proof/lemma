/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/CategoryTheory/Abelian/LeftDerived/Additive.lean -/

import Mathlib.CategoryTheory.Abelian.LeftDerived

/-!
# Additivity of projective resolutions and left-derived functors

The functor `projectiveResolutions C`, sending an object to (a choice of) its
projective resolution in the homotopy category, is additive. As a consequence,
the left-derived functors `F.leftDerived n` of an additive functor `F` are
additive.
-/

namespace CategoryTheory

open Category

universe v u

section

variable (C : Type u) [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]

/-- The functor sending an object to a choice of projective resolution is
additive: the lift of a sum of morphisms is homotopic to the sum of the lifts. -/
instance projectiveResolutions_additive : Functor.Additive (projectiveResolutions C) where
  map_add {X Y f g} := by
    dsimp [projectiveResolutions]
    suffices h : (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (f + g) (projectiveResolution X)
          (projectiveResolution Y)) =
      (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift f (projectiveResolution X) (projectiveResolution Y) +
         ProjectiveResolution.lift g (projectiveResolution X) (projectiveResolution Y)) by
      rw [h]
      exact (HomotopyCategory.quotient C (ComplexShape.down ℕ)).map_add
    apply HomotopyCategory.eq_of_homotopy
    apply ProjectiveResolution.liftHomotopy (f + g)
    · exact ProjectiveResolution.lift_commutes (f + g) _ _
    · rw [Preadditive.add_comp, ProjectiveResolution.lift_commutes f,
          ProjectiveResolution.lift_commutes g,
          ← Preadditive.comp_add, ← Functor.map_add]

end

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type*} [Category* D] [Abelian D]

/-- The left-derived functors of an additive functor are additive. -/
instance leftDerived_additive (F : C ⥤ D) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := by
  dsimp only [Functor.leftDerived, Functor.leftDerivedToHomotopyCategory]
  infer_instance

end

end CategoryTheory
