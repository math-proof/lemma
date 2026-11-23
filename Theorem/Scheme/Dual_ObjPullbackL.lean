module

public import Def.SheafOfModules_Monoidal

public noncomputable section

open CategoryTheory MonoidalCategory
set_option autoImplicit false


universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T P : Scheme.{u}}


public theorem rigidify_def (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) :
    rigidify σ q L = L ⊗ (Scheme.Modules.pullback q).obj
      (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) := rfl

