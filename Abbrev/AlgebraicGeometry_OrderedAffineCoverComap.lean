import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OrderedAffineCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Scheme.TwoAffineOpenCover

section Comap

variable {X Y : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (f : Y ⟶ X) [IsAffineHom f]


end Comap

section BaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒰 : X.OrderedAffineCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

abbrev baseChange : (Limits.pullback π (specMap R A)).OrderedAffineCover :=
  haveI := isAffineHom_fst π A
  𝒰.comap (Limits.pullback.fst π (specMap R A))

end BaseChange

end AlgebraicGeometry.Scheme.OrderedAffineCover

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (π : X ⟶ Spec (.of R))
  (A : Type u) [CommRing A] [Algebra R A]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
