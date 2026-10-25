import Mathlib
import Structure.JacJ1Iface
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Structure.AlgebraicGeometry_RelSubPicGroup
import Structure.AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

section Thickening

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

abbrev dualNumberReduction : Spec (.of A) ⟶ Spec (.of (DualNumber A)) :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R A A).toRingHom)

end Thickening

section Kernel

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A]

end Kernel

section KerPoints

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

end KerPoints

end AlgebraicGeometry.RelPicard

end
