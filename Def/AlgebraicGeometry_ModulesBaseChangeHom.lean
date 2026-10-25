import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}

def pullbackTwoSquare (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pullback ψ) (pullback π) (pullback π') (pullback g') :=
  (pullbackComp π' ψ).hom ≫ (pullbackCongr h.symm).hom ≫ (pullbackComp g' π).inv

def baseChangeNatTrans (h : g' ≫ π = π' ≫ ψ) :
    TwoSquare (pushforward π) (pullback g') (pullback ψ) (pushforward π') :=
  mateEquiv (pullbackPushforwardAdjunction π) (pullbackPushforwardAdjunction π') (pullbackTwoSquare h)

def baseChangeHom (h : g' ≫ π = π' ≫ ψ) (F : X.Modules) :
    (pullback ψ).obj ((pushforward π).obj F) ⟶ (pushforward π').obj ((pullback g').obj F) :=
  (baseChangeNatTrans h).natTrans.app F

end AlgebraicGeometry.Scheme.Modules

end
