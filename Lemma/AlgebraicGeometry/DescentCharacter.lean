import Mathlib
import Def.AlgebraicGeometry_DescentCharacter

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.DescentCharacter

variable {X Y : Scheme.{u}}


theorem transportNatIso_app {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (M : Y.Modules) :
    (transportNatIso h).app M = transportIso h M := rfl


variable {R : Type u} [CommRing R]


@[simp] theorem baseSectionRingHom_apply (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (c : R) :
    baseSectionRingHom f U c = baseSection f c U := rfl

@[simp] theorem baseSection_one (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : baseSection f 1 U = 1 := by
  rw [← baseSectionRingHom_apply, map_one]

@[simp] theorem baseSection_mul (f : X ⟶ Spec (CommRingCat.of R)) (c c' : R) (U : X.Opens) :
    baseSection f (c * c') U = baseSection f c U * baseSection f c' U := by
  simp only [← baseSectionRingHom_apply, map_mul]

theorem map_baseSection (f : X ⟶ Spec (CommRingCat.of R)) (c : R) {U V : X.Opens} (i : V ⟶ U) :
    X.presheaf.map i.op (baseSection f c U) = baseSection f c V := by
  unfold baseSection
  rw [← CategoryTheory.comp_apply, ← X.presheaf.map_comp]
  rfl

end AlgebraicGeometry.DescentCharacter

end
