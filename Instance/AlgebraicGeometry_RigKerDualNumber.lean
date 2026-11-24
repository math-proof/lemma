module
public import Mathlib
public import Structure.JacJ1Iface
public import Instance.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.RepresentsRelSubPic
public import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
public import Def.AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
public import Theorem.Scheme.RelSubPicGroup
public import Theorem.Scheme.TwoAffineOpenCover
public import Def.AlgebraicGeometry_RigKerDualNumber
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RigKerDualNumber.lean: instance decls only.

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

namespace AlgebraicGeometry.RelPicard


section Kernel

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A]

instance RigKerDualNumber.setoid : Setoid (RigKerDualNumber.Carrier c ε A) :=
  (RigidifiedLineBundle.setoid (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).comap
    Subtype.val

end Kernel


end AlgebraicGeometry.RelPicard

end
