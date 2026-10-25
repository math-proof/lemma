import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_PolarisationRosati
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Instance.AlgebraicGeometry_SymmRootFunctor

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

section base
variable (S : Type u) [CommRing S] (R₀ : Type u) [CommRing R₀] [Algebra S R₀]


end base

section functor
variable {S : Type u} [CommRing S] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of S))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

structure StablePred where

  P : ∀ (B : Under (CommRingCat.of R₀)), (pullback c (ι S R₀ B)).Modules → Prop

  of_pullbackAlong : ∀ {B B' : Under (CommRingCat.of R₀)} (φ : B ⟶ B') (M : RigidifiedLineBundle c ε (ι S R₀ B)),
    P B M.L → P B' (M.pullbackAlong (ψ S R₀ φ)).L

variable (P : StablePred c ε R₀)

structure Elem (B : Under (CommRingCat.of R₀)) where

  M : RigidifiedLineBundle c ε (ι S R₀ B)
  prop : P.P B M.L


end functor

section symmRoot
variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]


end symmRoot

end AlgebraicGeometry.SymmRoot

end
