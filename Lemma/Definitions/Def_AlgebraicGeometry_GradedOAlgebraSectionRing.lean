import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

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

structure IsSectionRing (f : X ⟶ Spec (CommRingCat.of S)) (L : X.Modules)
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) : Prop where

  bijective : ∀ n, Function.Bijective (ι n)

  map_add : ∀ n (x y : 𝓡 n), ι n (x + y) = ι n x + ι n y

  map_smul : ∀ n (s : S) (x : 𝓡 n), ι n (s • x) = baseScalar f s • ι n x

  map_one : ι 0 ⟨1, SetLike.GradedOne.one_mem⟩ = unitSection ⊤

  map_mul : ∀ m n (x : 𝓡 m) (y : 𝓡 n),
    ι (m + n) ⟨(x : R) * (y : R), SetLike.GradedMul.mul_mem x.2 y.2⟩ =
      ((tensorPowAdd L m n).hom.app ⊤) (tensorSections (ι m x) (ι n y))

end AlgebraicGeometry.GradedOAlgebra

end
