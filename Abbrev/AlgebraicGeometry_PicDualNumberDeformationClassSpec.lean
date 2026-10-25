import Mathlib
import Instance.AlgebraicGeometry_RigKerDualNumber
import Structure.AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Lemma.AlgebraicGeometry.ModulesSectionsTensor

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry.RelPicard

section Thickening

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

abbrev dualNumberThickening :
    HomOver (IsScalarTower.toAlgHom R A (DualNumber A)).toRingHom (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A))) :=
  HomOver.stage 𝒱 c (IsScalarTower.toAlgHom R A (DualNumber A))

end Thickening

section Spec

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

abbrev H1StructureSheaf : Type u :=
  ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1

end Spec

end AlgebraicGeometry.RelPicard

end
