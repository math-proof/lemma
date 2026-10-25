import Def.AlgebraicGeometry_RelPicardStageHom

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite NeronModelInfra

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {T : Type u} [CommRing T]

structure HomOver (τ : R →+* S) {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {Y : Scheme.{u}} (𝒲 : Y.TwoAffineOpenCover) (c' : Y ⟶ Spec (.of S)) where

  hom : Y ⟶ X
  comm : hom ≫ c = c' ≫ Spec.map (CommRingCat.ofHom τ)
  U0_le : 𝒲.U0 ≤ hom ⁻¹ᵁ 𝒱.U0
  U1_le : 𝒲.U1 ≤ hom ⁻¹ᵁ 𝒱.U1

namespace HomOver

variable {τ : R →+* S} {X : Scheme.{u}} {𝒱 : X.TwoAffineOpenCover} {c : X ⟶ Spec (.of R)}
  {Y : Scheme.{u}} {𝒲 : Y.TwoAffineOpenCover} {c' : Y ⟶ Spec (.of S)} (f : HomOver τ 𝒱 c 𝒲 c')


end HomOver

section BaseChange

variable {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
  {A : Type u} [CommRing A] [Algebra R A] {B : Type u} [CommRing B] [Algebra R B]
  {B' : Type u} [CommRing B'] [Algebra R B']

variable (A) in


variable (A) in


end BaseChange

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
