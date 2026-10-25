import Mathlib
import Instance.PresheafOfModules_ExteriorPower
import Abbrev.AlgebraicGeometry_ModulesDet

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))


abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehlerPresheaf


end AlgebraicGeometry.Scheme.Hom

end
