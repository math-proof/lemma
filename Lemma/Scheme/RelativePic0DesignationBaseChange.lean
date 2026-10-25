import Mathlib
import Structure.JacJ1Iface
import Instance.AlgebraicGeometry_SmoothProperCurveBase
import Abbrev.AlgebraicGeometry_RelativePic0DesignationBaseChange

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

namespace GoodReductionJacobian.RelativePic0Designation

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}


theorem baseChange_P : (D.baseChange R').P = pullback D.toBase (specMap R R') := rfl

theorem baseChange_toBase : (D.baseChange R').toBase = pullback.snd D.toBase (specMap R R') := rfl

theorem baseChange_zeroSection :
    (D.baseChange R').zeroSection = pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
      (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp]) := rfl

theorem baseChange_zeroSection_fst :
    (D.baseChange R').zeroSection ≫ pullback.fst D.toBase (specMap R R') = specMap R R' ≫ D.zeroSection :=
  pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativePic0Designation

end
