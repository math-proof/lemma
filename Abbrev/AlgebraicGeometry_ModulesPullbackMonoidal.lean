import Mathlib
import Instance.PresheafOfModules_InternalHom
import Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import Instance.SheafOfModules_Monoidal
import Instance.PresheafOfModules_PullbackMonoidal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)


abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

end AlgebraicGeometry.Scheme.Modules

end
