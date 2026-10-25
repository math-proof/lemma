import Mathlib
import Instance.AlgebraicGeometry_SymmRootFunctor

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

def admPred (B : Under (CommRingCat.of R₀)) (N : (pullback f (ι S R₀ B)).Modules) : Prop :=
  LocIsoOnBase (pullback.snd f (ι S R₀ B))
      ((Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj N) N ∧
    LocIsoOnBase (pullback.snd f (ι S R₀ B)) (N ⊗ N) (𝟙_ ((pullback f (ι S R₀ B)).Modules))

end AlgebraicGeometry.SymmRoot

end
