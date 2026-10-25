import Mathlib
import Abbrev.SheafOfModules_MonoidalV2

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

def tensorPowAdd (L : X.Modules) (m : ℕ) : (n : ℕ) → (L.tensorPow m ⊗ L.tensorPow n ≅ L.tensorPow (m + n))
  | 0 => ρ_ (L.tensorPow m)
  | n + 1 => (α_ (L.tensorPow m) (L.tensorPow n) L).symm ≪≫ whiskerRightIso (tensorPowAdd L m n) L

def tensorPowMapIso {L₁ L₂ : X.Modules} (e : L₁ ≅ L₂) : (n : ℕ) → (L₁.tensorPow n ≅ L₂.tensorPow n)
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowMapIso e n) e

def pullbackTensorPowIso {Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules) :
    (n : ℕ) → ((Modules.pullback c).obj (L.tensorPow n) ≅ ((Modules.pullback c).obj L).tensorPow n)
  | 0 => pullbackTensorUnitObjIso c
  | n + 1 => pullbackTensorObjIso c (L.tensorPow n) L ≪≫ whiskerRightIso (pullbackTensorPowIso c L n) ((Modules.pullback c).obj L)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.GradedOAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}}

def baseScalar (f : X ⟶ Spec (CommRingCat.of S)) (s : S) : Γ(X, ⊤) :=
  f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom s)

end AlgebraicGeometry.GradedOAlgebra

end
