import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Lemma.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Lemma.Definitions.Def_JacJ1Iface
import Lemma.Definitions.Def_SheafOfModules_Monoidal
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

def RigidifiedLineBundle.tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (L M : RigidifiedLineBundle c ε t) : RigidifiedLineBundle c ε t where
  L := L.L ⊗ M.L
  isInvertible := L.isInvertible.tensor M.isInvertible
  rigidified := ⟨(Scheme.Modules.pullbackTensorObjIso _ _ _) ≪≫ (L.rigidified.some ⊗ᵢ M.rigidified.some) ≪≫ λ_ _⟩

theorem RigidifiedLineBundle.tensor_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L L' M M' : RigidifiedLineBundle c ε t} (hL : L ≈ L') (hM : M ≈ M') : L.tensor M ≈ L'.tensor M' :=
  ⟨Nonempty.some (hL : Nonempty (L.L ≅ L'.L)) ⊗ᵢ Nonempty.some (hM : Nonempty (M.L ≅ M'.L))⟩

theorem RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (L M : RigidifiedLineBundle c ε t) :
    Nonempty (((L.tensor M).pullbackAlong ψ).L ≅ ((L.pullbackAlong ψ).tensor (M.pullbackAlong ψ)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩

theorem RigidifiedLineBundle.exists_tensor_iso_unit {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (L : RigidifiedLineBundle c ε t) :
    ∃ M : RigidifiedLineBundle c ε t, Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := L.isInvertible.exists_tensor_inverse
  refine ⟨⟨N, hN, ⟨?_⟩⟩, ⟨e⟩⟩
  exact (λ_ _).symm ≪≫ (L.rigidified.some.symm ⊗ᵢ Iso.refl _) ≪≫
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _

structure SubPicGroupCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) extends SubPicCondition c ε where
  tensor_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t),
    P t L → P t M → P t (L.tensor M)
  inv_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t),
    Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) → P t L → P t M

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

theorem RepresentsRelSubPic.homEquiv_mul {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) (T : Over (Spec (CommRingCat.of R)))
    (a b : T ⟶ Over.mk D.toBase) :
    letI := h.grpObj
    letI := P.commGroupObj (Opposite.op T)
    h.representableBy.homEquiv (a * b) = h.representableBy.homEquiv a * h.representableBy.homEquiv b := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op T)
  letI := P.commGroupObj (Opposite.op (Over.mk D.toBase ⊗ Over.mk D.toBase))
  have hμ := MonObj.ofRepresentableBy_mul (Over.mk D.toBase)
    ((relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget₂ GrpCat MonCat) h.grpRepresentableBy

  have hμ' : h.representableBy.homEquiv (μ[Over.mk D.toBase]) =
      h.representableBy.homEquiv (CartesianMonoidalCategory.fst (Over.mk D.toBase) (Over.mk D.toBase)) *
        h.representableBy.homEquiv (CartesianMonoidalCategory.snd (Over.mk D.toBase) (Over.mk D.toBase)) := by
    conv_lhs => rw [hμ]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.mul_def, h.representableBy.homEquiv_comp, hμ']
  change ((relSubPicCommGrpPresheaf c ε P).map (CartesianMonoidalCategory.lift a b).op).hom (_ * _) = _
  rw [map_mul]
  change (relSubPicPresheaf c ε P.toSubPicCondition).map _ (h.representableBy.homEquiv _) *
      (relSubPicPresheaf c ε P.toSubPicCondition).map _ (h.representableBy.homEquiv _) = _
  rw [← h.representableBy.homEquiv_comp, ← h.representableBy.homEquiv_comp,
    CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  rfl

theorem RepresentsRelSubPic.homEquiv_one {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) (T : Over (Spec (CommRingCat.of R))) :
    letI := h.grpObj
    letI := P.commGroupObj (Opposite.op T)
    h.representableBy.homEquiv (1 : T ⟶ Over.mk D.toBase) = 1 := by
  letI := h.grpObj
  letI := P.commGroupObj (Opposite.op T)
  letI := P.commGroupObj (Opposite.op (𝟙_ (Over (Spec (CommRingCat.of R)))))
  have hη := MonObj.ofRepresentableBy_one (Over.mk D.toBase)
    ((relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget₂ GrpCat MonCat) h.grpRepresentableBy
  have hη' : h.representableBy.homEquiv (η[Over.mk D.toBase]) = 1 := by
    conv_lhs => rw [hη]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.one_def, h.representableBy.homEquiv_comp, hη']
  change ((relSubPicCommGrpPresheaf c ε P).map (CartesianMonoidalCategory.toUnit T).op).hom 1 = 1
  exact map_one _

theorem RepresentsRelSubPic.isCommMonObj {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    letI := h.grpObj
    IsCommMonObj (Over.mk D.toBase) := by
  letI := h.grpObj
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  letI := P.commGroupObj (Opposite.op T)
  refine ⟨⟨fun a b => h.representableBy.homEquiv.injective ?_⟩⟩
  rw [h.homEquiv_mul, h.homEquiv_mul, mul_comm]

theorem RepresentsRelSubPic.relativeGroupLaw_isCommutative {P : SubPicGroupCondition c ε}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    h.relativeGroupLaw.IsCommutative := by
  letI := h.grpObj
  intro T t x y
  exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h.isCommMonObj t x y

theorem RepresentsRelSubPic.relativeGroupLaw_one {P : SubPicGroupCondition c ε}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    (h.relativeGroupLaw.one (𝟙 _)).1 = D.zeroSection := by
  letI := h.grpObj
  have h1 := h.homEquiv_one (Over.mk (𝟙 _))
  have h2 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase) =
      h.representableBy.homEquiv.symm ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), P.unit_mem _⟩ := by
    apply h.representableBy.homEquiv.injective
    rw [h1, Equiv.apply_symm_apply]
    rfl
  have h3 : (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 _) D.toBase) =
      h.classifyClass (𝟙 _) (relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _))) (P.unit_mem _) :=
    h.eq_classifyClass _ _ _ _ (Quotient.sound h.zero)
  change (overHomToSchemeHomOver (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase)).1 = _
  rw [h2]
  exact (congrArg Subtype.val h3).symm

end AlgebraicGeometry.RelPicard

end
