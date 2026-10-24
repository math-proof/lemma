import Mathlib
import Lemma.Definitions.Def_SheafOfModules_Monoidal
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : Scheme.{u}} (i : Z ⟶ X)

def projectionMorphismMate (F : X.Modules) :
    (Modules.pullback i).obj ((Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F) ⟶ (Modules.pullback i).obj F :=
  (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
    ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
    (λ_ ((Modules.pullback i).obj F)).hom

def projectionMorphism (F : X.Modules) :
    (Modules.pushforward i).obj (𝟙_ Z.Modules) ⊗ F ⟶ (Modules.pushforward i).obj ((Modules.pullback i).obj F) :=
  ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F)

theorem projectionMorphism_def (F : X.Modules) :
    projectionMorphism i F = ((pullbackPushforwardAdjunction i).homEquiv _ _) (projectionMorphismMate i F) := rfl

theorem projectionMorphismMate_def (F : X.Modules) :
    projectionMorphismMate i F =
      (Functor.Monoidal.μIso (Modules.pullback i) ((Modules.pushforward i).obj (𝟙_ Z.Modules)) F).inv ≫
        ((pullbackPushforwardAdjunction i).counit.app (𝟙_ Z.Modules) ▷ (Modules.pullback i).obj F) ≫
        (λ_ ((Modules.pullback i).obj F)).hom := rfl

end AlgebraicGeometry.Scheme.Modules

end
