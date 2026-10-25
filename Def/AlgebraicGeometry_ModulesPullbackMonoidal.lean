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


def pullbackTensorObjIso (L M : Y.Modules) :
    (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M :=
  (Functor.Monoidal.μIso (Modules.pullback f) L M).symm

def pullbackTensorUnitObjIso : (Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (Functor.Monoidal.εIso (Modules.pullback f)).symm

end AlgebraicGeometry.Scheme.Modules

end
