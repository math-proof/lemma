import Mathlib
import Instance.PresheafOfModules_ExteriorPower

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

noncomputable abbrev presheafExteriorPower (n : ℕ) : X.PresheafOfModules ⥤ X.PresheafOfModules :=
  _root_.PresheafOfModules.exteriorPowerFunctor X.sheaf.obj n


end AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})


variable {X} in

noncomputable abbrev det (n : ℕ) (M : X.Modules) : X.Modules := (exteriorPower X n).obj M

end AlgebraicGeometry.Scheme.Modules
