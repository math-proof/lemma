import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Structure.JacJ1Iface

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian Scheme

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
  (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)

def curveChange {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : pullback c' t ⟶ pullback c t :=
  pullback.map c' t c t f (𝟙 T) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)

include hε in
def RigidifiedLineBundle.pullbackCurve {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c' ε' t where
  L := (Scheme.Modules.pullback (curveChange f hf t)).obj M.L
  isInvertible := M.isInvertible.pullback _
  rigidified := ⟨(Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (rigSection_curveChange f hf hε t)).app M.L ≪≫ M.rigidified.some⟩

def RigidifiedLineBundle.pullbackCurvePullbackAlongIso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) :
    ((M.pullbackCurve f hf hε).pullbackAlong ψ).L ≅ ((M.pullbackAlong ψ).pullbackCurve f hf hε).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (curveChange_baseChangeSnd f hf ψ).symm).app M.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M.L).symm

def RigidifiedLineBundle.pullbackAlongPullbackAlongIso' {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (ψ : SchemeHomOver t' t) (φ : SchemeHomOver t'' t') :
    ((M.pullbackAlong ψ).pullbackAlong φ).L ≅ (M.pullbackAlong (postComp ψ φ)).L :=
  (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ψ φ)).app M.L

def RigidifiedLineBundle.unitPullbackCurveIso {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    ((RigidifiedLineBundle.unit (c := c) (ε := ε) t).pullbackCurve f hf hε).L ≅
      (RigidifiedLineBundle.unit (c := c') (ε := ε') t).L :=
  Scheme.Modules.pullbackUnitIso _

include hf in
namespace RepresentsRelSubPic

variable {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')

def pullbackHom : SchemeHomOver D.toBase D'.toBase :=
  h'.classify D.toBase (h.poincare.pullbackCurve f hf hε) (FibrewiseAlgEquivZero.pullbackCurve f hf hε h.poincare_mem)

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard

end
