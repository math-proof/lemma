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


abbrev admStablePred
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (N : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (ψ S R₀ φ)).L) :
    StablePred f (L.one (𝟙 _)) R₀ :=
  ⟨admPred L R₀, h⟩

end AlgebraicGeometry.SymmRoot

end
