import Mathlib
import Abbrev.AlgebraicGeometry_ModulesDet
import Instance.SheafOfModules_Monoidal

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

def normModule (π : X ⟶ Y) (d : ℕ) (L : X.Modules) : Y.Modules :=
  det d ((pushforward π).obj L) ⊗ dual (det d ((pushforward π).obj (𝟙_ X.Modules)))


def normModuleFunctor (π : X ⟶ Y) (d : ℕ) : X.Modules ⥤ Y.Modules :=
  (pushforward π ⋙ exteriorPower Y d) ⋙ tensorRight (dual (det d ((pushforward π).obj (𝟙_ X.Modules))))


def normModuleMapIso (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (e : L ≅ L') :
    normModule π d L ≅ normModule π d L' :=
  (normModuleFunctor π d).mapIso e

def dualCongr {A B : Y.Modules} (e : A ≅ B) : dual A ≅ dual B where
  hom := (MonoidalClosed.pre e.inv).app (𝟙_ Y.Modules)
  inv := (MonoidalClosed.pre e.hom).app (𝟙_ Y.Modules)
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id, MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id, MonoidalClosed.pre_id, NatTrans.id_app]

def normModuleIdIso (d : ℕ) (L : X.Modules) :
    normModule (𝟙 X) d L ≅ det d L ⊗ dual (det d (𝟙_ X.Modules)) :=
  ((exteriorPower X d).mapIso ((pushforwardId X).app L)) ⊗ᵢ
    dualCongr ((exteriorPower X d).mapIso ((pushforwardId X).app (𝟙_ X.Modules)))

def normModuleCongr {π π' : X ⟶ Y} (h : π = π') (d : ℕ) (L : X.Modules) :
    normModule π d L ≅ normModule π' d L :=
  ((exteriorPower Y d).mapIso ((pushforwardCongr h).app L)) ⊗ᵢ
    dualCongr ((exteriorPower Y d).mapIso ((pushforwardCongr h).app (𝟙_ X.Modules)))


def normModuleUnitEval (π : X ⟶ Y) (d : ℕ) : normModule π d (𝟙_ X.Modules) ⟶ 𝟙_ Y.Modules :=
  (ihom.ev (det d ((pushforward π).obj (𝟙_ X.Modules)))).app (𝟙_ Y.Modules)

end AlgebraicGeometry.Scheme.Modules

end
