import Mathlib
import Def.AlgebraicGeometry_RelativePicardFunctor
import Def.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelSubPicPresheaf
import Lemma.Scheme.RelativeGroupLawGrpObj
import Structure.JacJ1Iface
import Instance.SheafOfModules_Monoidal
import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import Structure.AlgebraicGeometry_RelSubPicGroup

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard Scheme
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}


def SubPicGroupCondition.mulObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ)
    (x y : (relSubPicPresheaf c ε P.toSubPicCondition).obj X) :
    (relSubPicPresheaf c ε P.toSubPicCondition).obj X :=
  ⟨Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM) x.1 y.1, by
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    induction x using Quotient.ind
    induction y using Quotient.ind
    exact P.tensor_mem _ _ _ hx hy⟩

def SubPicGroupCondition.oneObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    (relSubPicPresheaf c ε P.toSubPicCondition).obj X :=
  ⟨relPicardPresheaf.unitClass c ε X.unop, P.unit_mem _⟩

def SubPicGroupCondition.invObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ)
    (x : (relSubPicPresheaf c ε P.toSubPicCondition).obj X) :
    (relSubPicPresheaf c ε P.toSubPicCondition).obj X :=
  ⟨Quotient.mk _ (RigidifiedLineBundle.exists_tensor_iso_unit x.1.out).choose,
    P.inv_mem _ x.1.out _ (RigidifiedLineBundle.exists_tensor_iso_unit x.1.out).choose_spec
      (by have hx := x.2; rw [← Quotient.out_eq x.1] at hx; exact hx)⟩

@[reducible]
def SubPicGroupCondition.commGroupObj (P : SubPicGroupCondition c ε) (X : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    CommGroup ((relSubPicPresheaf c ε P.toSubPicCondition).obj X) where
  mul := P.mulObj X
  one := P.oneObj X
  inv := P.invObj X
  mul_assoc := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
    apply Subtype.ext
    induction x using Quotient.ind
    induction y using Quotient.ind
    induction z using Quotient.ind
    exact Quotient.sound ⟨α_ _ _ _⟩
  one_mul := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    induction x using Quotient.ind
    exact Quotient.sound ⟨λ_ _⟩
  mul_one := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    induction x using Quotient.ind
    exact Quotient.sound ⟨ρ_ _⟩
  mul_comm := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    induction x using Quotient.ind
    induction y using Quotient.ind
    exact Quotient.sound ⟨β_ _ _⟩
  inv_mul_cancel := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    have key : ∀ (L₀ M : RigidifiedLineBundle c ε X.unop.hom),
        Nonempty ((L₀.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) X.unop.hom).L) →
        Quotient.map₂ (fun L M => L.tensor M) (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
          (Quotient.mk _ M : RigidifiedLineBundle.Classes c ε X.unop.hom)
          (Quotient.mk _ L₀ : RigidifiedLineBundle.Classes c ε X.unop.hom) =
        (Quotient.mk _ (RigidifiedLineBundle.unit X.unop.hom) : RigidifiedLineBundle.Classes c ε X.unop.hom) :=
      fun L₀ M hM => Quotient.sound ⟨β_ _ _ ≪≫ hM.some⟩
    have h := key x.out _ (RigidifiedLineBundle.exists_tensor_iso_unit x.out).choose_spec
    rw [Quotient.out_eq] at h
    exact h

def relSubPicCommGrpPresheaf (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicGroupCondition c ε) : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1} where
  obj X := @CommGrpCat.of ((relSubPicPresheaf c ε P.toSubPicCondition).obj X) (P.commGroupObj X)
  map {X X'} φ :=
    letI := P.commGroupObj X
    letI := P.commGroupObj X'
    CommGrpCat.ofHom
      { toFun := (relSubPicPresheaf c ε P.toSubPicCondition).map φ
        map_one' := by
          apply Subtype.ext
          exact Quotient.sound ⟨Scheme.Modules.pullbackUnitIso _⟩
        map_mul' := by
          rintro ⟨x, hx⟩ ⟨y, hy⟩
          apply Subtype.ext
          induction x using Quotient.ind
          induction y using Quotient.ind
          exact Quotient.sound (RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso _ _ _) }
  map_id X := by
    letI := P.commGroupObj X
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    simp
  map_comp {X X' X''} φ ψ := by
    letI := P.commGroupObj X
    letI := P.commGroupObj X'
    letI := P.commGroupObj X''
    refine CommGrpCat.hom_ext (MonoidHom.ext fun x => ?_)
    simp

def RepresentsRelSubPic.grpRepresentableBy {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    ((relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy
      (Over.mk D.toBase) where
  homEquiv := h.representableBy.homEquiv
  homEquiv_comp f g := h.representableBy.homEquiv_comp f g

@[reducible]
def RepresentsRelSubPic.grpObj {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) : GrpObj (Over.mk D.toBase) :=
  GrpObj.ofRepresentableBy (Over.mk D.toBase) (relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat)
    h.grpRepresentableBy

def RepresentsRelSubPic.relativeGroupLaw {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) : RelativeGroupLaw R D.toBase :=
  letI := h.grpObj
  relativeGroupLawOfGrpObj R D.toBase

end AlgebraicGeometry.RelPicard

end
