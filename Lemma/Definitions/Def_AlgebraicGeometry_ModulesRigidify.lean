import Lemma.Definitions.Def_SheafOfModules_Monoidal

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory

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
