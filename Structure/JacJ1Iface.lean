import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Structure.AlgebraicGeometry_RelativeGroupLaw

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

open NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]

structure AbelianSchemePropertyBundle {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R)) :
    Prop where

  smooth : Smooth f

  proper : IsProper f

  connectedFibres : ∀ s : Spec (CommRingCat.of R), _root_.IsConnected (f.base ⁻¹' {s})

  hasGroupLaw : Nonempty (RelativeGroupLaw R f)

structure RelativePic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) where

  P : Scheme.{u}

  toBase : P ⟶ Spec (CommRingCat.of R)

  zeroSection : Spec (CommRingCat.of R) ⟶ P

  zeroSection_toBase : zeroSection ≫ toBase = 𝟙 (Spec (CommRingCat.of R))

end AbstractCarriers
end GoodReductionJacobian
end
