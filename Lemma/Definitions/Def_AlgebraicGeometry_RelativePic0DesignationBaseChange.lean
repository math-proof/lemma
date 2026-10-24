import Mathlib
import Lemma.Definitions.Def_JacJ1Iface
import Lemma.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

namespace GoodReductionJacobian.RelativePic0Designation

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

abbrev baseChange (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R'] :
    RelativePic0Designation R' (SmoothProperCurve.baseChange R c R') where
  P := pullback D.toBase (specMap R R')
  toBase := pullback.snd D.toBase (specMap R R')
  zeroSection := pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
    (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp])
  zeroSection_toBase := pullback.lift_snd _ _ _

variable (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']

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
