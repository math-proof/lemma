module

public import Mathlib
public import Def.AlgebraicGeometry_RelativePicardFunctor
public import Theorem.Scheme.RepresentsRelSubPic
public import Def.AlgebraicGeometry_RelSubPicPresheaf
public import Theorem.Scheme.RelativeGroupLawGrpObj
public import Structure.JacJ1Iface
public import Instance.SheafOfModules_Monoidal
public import Instance.AlgebraicGeometry_ModulesPullbackMonoidal
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
public import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
public import Structure.AlgebraicGeometry_RelSubPicGroup

public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard Scheme
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}


public theorem RigidifiedLineBundle.tensor_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L L' M M' : RigidifiedLineBundle c ε t} (hL : L ≈ L') (hM : M ≈ M') : L.tensor M ≈ L'.tensor M' :=
  ⟨Nonempty.some (hL : Nonempty (L.L ≅ L'.L)) ⊗ᵢ Nonempty.some (hM : Nonempty (M.L ≅ M'.L))⟩


public theorem RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (ψ : SchemeHomOver t' t) (L M : RigidifiedLineBundle c ε t) :
    Nonempty (((L.tensor M).pullbackAlong ψ).L ≅ ((L.pullbackAlong ψ).tensor (M.pullbackAlong ψ)).L) :=
  ⟨Scheme.Modules.pullbackTensorObjIso _ _ _⟩


public theorem RigidifiedLineBundle.exists_tensor_iso_unit {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (L : RigidifiedLineBundle c ε t) :
    ∃ M : RigidifiedLineBundle c ε t, Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := L.isInvertible.exists_tensor_inverse
  refine ⟨⟨N, hN, ⟨?_⟩⟩, ⟨e⟩⟩
  exact (λ_ _).symm ≪≫ (L.rigidified.some.symm ⊗ᵢ Iso.refl _) ≪≫
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _


public theorem RepresentsRelSubPic.homEquiv_mul {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
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


public theorem RepresentsRelSubPic.homEquiv_one {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
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


public theorem RepresentsRelSubPic.isCommMonObj {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    letI := h.grpObj
    IsCommMonObj (Over.mk D.toBase) := by
  letI := h.grpObj
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  letI := P.commGroupObj (Opposite.op T)
  refine ⟨⟨fun a b => h.representableBy.homEquiv.injective ?_⟩⟩
  rw [h.homEquiv_mul, h.homEquiv_mul, mul_comm]


public theorem RepresentsRelSubPic.relativeGroupLaw_isCommutative {P : SubPicGroupCondition c ε}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    h.relativeGroupLaw.IsCommutative := by
  letI := h.grpObj
  intro T t x y
  exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h.isCommMonObj t x y


public theorem RepresentsRelSubPic.relativeGroupLaw_one {P : SubPicGroupCondition c ε}
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
