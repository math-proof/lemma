import Def.SheafOfModules_Monoidal
open CategoryTheory MonoidalCategory
set_option autoImplicit false


universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T P : Scheme.{u}}

def dualMapIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

def rigidify (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) : P.Modules :=
  L ⊗ (Scheme.Modules.pullback q).obj
    (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L))

lemma rigidify_def (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules) :
    rigidify σ q L = L ⊗ (Scheme.Modules.pullback q).obj
      (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) := rfl

def rigidifyMapIso (σ : T ⟶ P) (q : P ⟶ T) {L L' : P.Modules} (e : L ≅ L') :
    rigidify σ q L ≅ rigidify σ q L' :=
  e ⊗ᵢ (Scheme.Modules.pullback q).mapIso (dualMapIso ((Scheme.Modules.pullback σ).mapIso e))

end AlgebraicGeometry.Scheme.Modules

end

-- created on 2026-10-24
-- updated on 2026-10-24
