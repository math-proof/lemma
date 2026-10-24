import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_SymmRootFunctor

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

theorem admPred_iff (B : Under (CommRingCat.of R₀)) (N : (pullback f (ι S R₀ B)).Modules) :
    admPred L R₀ B N ↔
      LocIsoOnBase (pullback.snd f (ι S R₀ B))
          ((Scheme.Modules.pullback (negMor (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)))).obj N) N ∧
        LocIsoOnBase (pullback.snd f (ι S R₀ B)) (N ⊗ N) (𝟙_ ((pullback f (ι S R₀ B)).Modules)) :=
  Iff.rfl

theorem admPred_iff' (B : Under (CommRingCat.of R₀)) (N : (pullback f (ι S R₀ B)).Modules) :
    admPred L R₀ B N ↔
      IsSymmetric (pullback.snd f (ι S R₀ B)) (L.baseChange (ι S R₀ B)) N ∧
        LocIsoOnBase (pullback.snd f (ι S R₀ B)) (N ⊗ N) (𝟙_ ((pullback f (ι S R₀ B)).Modules)) :=
  Iff.rfl

abbrev admStablePred
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (N : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (ψ S R₀ φ)).L) :
    StablePred f (L.one (𝟙 _)) R₀ :=
  ⟨admPred L R₀, h⟩

example
    (h : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (N : RigidifiedLineBundle f (L.one (𝟙 _)) (ι S R₀ B)),
      admPred L R₀ B N.L → admPred L R₀ B' (N.pullbackAlong (ψ S R₀ φ)).L)
    (B : Under (CommRingCat.of R₀)) :
    (admStablePred L R₀ h).P B = admPred L R₀ B := rfl

end AlgebraicGeometry.SymmRoot

end
