import Structure.AlgebraicGeometry_TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Structure.AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite


namespace Scheme.TwoAffineOpenCover

abbrev specMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

section Pullback

variable (A : Type u) [CommRing A] [Algebra R A]

end Pullback

end Scheme.TwoAffineOpenCover

end AlgebraicGeometry

end
