import Mathlib
import Lemma.Definitions.Def_PresheafOfModules_InternalHom
import Lemma.Definitions.Def_SheafOfModules_MonoidalV2
import Lemma.Definitions.Def_PresheafOfModules_PullbackMonoidal
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

end AlgebraicGeometry.Scheme.Modules

end
