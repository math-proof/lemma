import Mathlib
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_PolarisationRosati
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

namespace AlgebraicGeometry.SymmRoot

section base
variable (S : Type u) [CommRing S] (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

abbrev algS (B : Under (CommRingCat.of R₀)) : Algebra S B.right := (B.hom.hom.comp (algebraMap S R₀)).toAlgebra

end base

section functor
variable {S : Type u} [CommRing S] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of S))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) c) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]


variable (P : StablePred c ε R₀)


end functor

section symmRoot
variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}
  (L : RelativeGroupLaw S f) (𝓛 : A.Modules) (R₀ : Type u) [CommRing R₀] [Algebra S R₀]

end symmRoot

end AlgebraicGeometry.SymmRoot

end
