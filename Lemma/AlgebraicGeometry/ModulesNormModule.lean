import Mathlib
import Abbrev.AlgebraicGeometry_ModulesDet
import Instance.SheafOfModules_Monoidal
import Def.AlgebraicGeometry_ModulesNormModule

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}


theorem normModule_def (π : X ⟶ Y) (d : ℕ) (L : X.Modules) :
    normModule π d L = det d ((pushforward π).obj L) ⊗ dual (det d ((pushforward π).obj (𝟙_ X.Modules))) := rfl


@[simp] theorem normModuleFunctor_obj (π : X ⟶ Y) (d : ℕ) (L : X.Modules) :
    (normModuleFunctor π d).obj L = normModule π d L := rfl

theorem normModuleFunctor_map (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (f : L ⟶ L') :
    (normModuleFunctor π d).map f =
      (exteriorPower Y d).map ((pushforward π).map f) ▷ dual (det d ((pushforward π).obj (𝟙_ X.Modules))) := rfl


theorem normModule_tensorUnit (π : X ⟶ Y) (d : ℕ) :
    normModule π d (𝟙_ X.Modules) =
      det d ((pushforward π).obj (𝟙_ X.Modules)) ⊗ dual (det d ((pushforward π).obj (𝟙_ X.Modules))) := rfl

end AlgebraicGeometry.Scheme.Modules

end
