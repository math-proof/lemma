import Mathlib
import Abbrev.SheafOfModules_MonoidalV2
import Def.AlgebraicGeometry_GradedOAlgebraSectionRing

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite

noncomputable section


namespace AlgebraicGeometry.GradedOAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {S : Type u} [CommRing S] {X : Scheme.{u}}


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
