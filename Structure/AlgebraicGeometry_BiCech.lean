import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Instance.AlgebraicGeometry_DoubleComplex
import Instance.AlgebraicGeometry_BiCech

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

structure Scheme.OrderedOpenFamily (Z : Scheme.{u}) where

  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]

  U : ι → Z.Opens

attribute [instance] Scheme.OrderedOpenFamily.instFintype Scheme.OrderedOpenFamily.instLinearOrder

namespace Scheme.OrderedOpenFamily

variable {Z : Scheme.{u}} (𝔄 : Z.OrderedOpenFamily)


end Scheme.OrderedOpenFamily

namespace Scheme.OrderedAffineCover


end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} {π : Z ⟶ Spec (.of R)} (F : OModulePresheaf π)
variable (𝔄 𝔅 : Z.OrderedOpenFamily)

namespace BiCech


end BiCech


end OModulePresheaf

end AlgebraicGeometry

end
