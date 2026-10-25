import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Abbrev.AlgebraicGeometry_SmoothProperCurveBase

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

namespace AlgebraicGeometry


namespace SmoothProperCurve

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))

section BaseChange

variable (T : Type u) [CommRing T] [Algebra R T]

def sectionBaseChange (ε : SchemeHomOver (𝟙 _) c) : SchemeHomOver (𝟙 _) (baseChange R c T) :=
  ⟨pullback.lift (specMap R T ≫ ε.1) (𝟙 _) (by rw [Category.assoc, ε.2]; simp),
    pullback.lift_snd _ _ _⟩

@[simp]
theorem sectionBaseChange_coe_fst (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.fst c (specMap R T) = specMap R T ≫ ε.1 :=
  pullback.lift_fst _ _ _

@[simp]
theorem sectionBaseChange_coe_snd (ε : SchemeHomOver (𝟙 _) c) :
    (sectionBaseChange T ε).1 ≫ pullback.snd c (specMap R T) = 𝟙 _ :=
  pullback.lift_snd _ _ _

end BaseChange


end SmoothProperCurve

end AlgebraicGeometry

end
