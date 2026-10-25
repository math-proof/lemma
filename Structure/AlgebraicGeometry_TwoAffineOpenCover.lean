import Structure.AlgebraicGeometry_TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

structure Scheme.TwoAffineOpenCover (X : Scheme.{u}) where

  U0 : X.Opens

  U1 : X.Opens
  isAffineOpen_U0 : IsAffineOpen U0
  isAffineOpen_U1 : IsAffineOpen U1
  sup_eq_top : U0 ⊔ U1 = ⊤
  isAffineOpen_inf : IsAffineOpen (U0 ⊓ U1)

namespace Scheme.TwoAffineOpenCover


variable {R : Type u} [CommRing R] {X : Scheme.{u}}


variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))


section Pullback

variable (A : Type u) [CommRing A] [Algebra R A]


end Pullback

end Scheme.TwoAffineOpenCover

end AlgebraicGeometry

end
