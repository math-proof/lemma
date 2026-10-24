import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Lemma.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Lemma.Definitions.Def_SheafOfModules_Monoidal
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

theorem GeometricallyIntegral.fst_comp_of_field {k : Type u} [Field k] {T₁ T₂ : Scheme.{u}}
    (h₁ : T₁ ⟶ Spec (CommRingCat.of k)) (h₂ : T₂ ⟶ Spec (CommRingCat.of k))
    [GeometricallyIntegral h₁] [LocallyOfFiniteType h₁] [GeometricallyIntegral h₂] [LocallyOfFiniteType h₂] :
    GeometricallyIntegral (pullback.fst h₁ h₂ ≫ h₁) := by
  constructor
  intro K _ y Z fst' snd' hP

  haveI : AlgebraicGeometry.IsIntegral (Limits.pullback h₁ y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := h₁) y (pullback.fst h₁ y) (pullback.snd h₁ y)
      (IsPullback.of_hasPullback h₁ y)

  haveI : AlgebraicGeometry.IsIntegral (Limits.pullback (pullback.fst h₁ h₂) (pullback.fst h₁ y)) := inferInstance

  exact AlgebraicGeometry.IsIntegral.of_isIso
    (pullbackRightPullbackFstIso h₁ y (pullback.fst h₁ h₂) ≪≫ hP.isoPullback.symm).hom

end AlgebraicGeometry

namespace AlgebraicGeometry.RelPicard

theorem IsAlgEquivZero.tensor {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L M : A.Modules} (hL : IsAlgEquivZero a L) (hM : IsAlgEquivZero a M) : IsAlgEquivZero a (L ⊗ M) := by
  obtain ⟨T₁, h₁, hft₁, hgi₁, N₁, hN₁, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL
  obtain ⟨T₂, h₂, hft₂, hgi₂, N₂, hN₂, s₀, s₁, ⟨f₀⟩, ⟨f₁⟩⟩ := hM

  let T := Limits.pullback h₁ h₂
  let h : T ⟶ Spec (CommRingCat.of k) := pullback.fst h₁ h₂ ≫ h₁
  haveI : LocallyOfFiniteType h := inferInstance
  haveI : GeometricallyIntegral h := GeometricallyIntegral.fst_comp_of_field h₁ h₂

  let p₁ : Limits.pullback a h ⟶ Limits.pullback a h₁ :=
    pullback.map a h a h₁ (𝟙 A) (pullback.fst h₁ h₂) (𝟙 _) (by simp) (by simp [h])
  let p₂ : Limits.pullback a h ⟶ Limits.pullback a h₂ :=
    pullback.map a h a h₂ (𝟙 A) (pullback.snd h₁ h₂) (𝟙 _) (by simp) (by simp [h, pullback.condition])

  have hts : ∀ (tt : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₁)
      (ss : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₂), tt.1 ≫ h₁ = ss.1 ≫ h₂ := fun tt ss => by
    rw [tt.2, ss.2]
  let u : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₁ → SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h₂ →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) h := fun tt ss =>
    ⟨pullback.lift tt.1 ss.1 (hts tt ss), by simp only [h, pullback.lift_fst_assoc]; exact tt.2⟩

  have hsq₁ : ∀ tt ss, baseChangeSnd a (u tt ss) ≫ p₁ = baseChangeSnd a tt := by
    intro tt ss
    apply pullback.hom_ext <;>
      simp only [p₁, u, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id]
  have hsq₂ : ∀ tt ss, baseChangeSnd a (u tt ss) ≫ p₂ = baseChangeSnd a ss := by
    intro tt ss
    apply pullback.hom_ext <;>
      simp only [p₂, u, baseChangeSnd, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id]

  refine ⟨T, h, inferInstance, inferInstance,
    (Scheme.Modules.pullback p₁).obj N₁ ⊗ (Scheme.Modules.pullback p₂).obj N₂,
    (hN₁.pullback p₁).tensor (hN₂.pullback p₂), u t₀ s₀, u t₁ s₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      ((((Scheme.Modules.pullbackComp _ _).app N₁ ≪≫ (Scheme.Modules.pullbackCongr (hsq₁ t₀ s₀)).app N₁ ≪≫ e₀) ⊗ᵢ
        ((Scheme.Modules.pullbackComp _ _).app N₂ ≪≫ (Scheme.Modules.pullbackCongr (hsq₂ t₀ s₀)).app N₂ ≪≫ f₀))) ≪≫
      λ_ _
  · exact Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
      ((((Scheme.Modules.pullbackComp _ _).app N₁ ≪≫ (Scheme.Modules.pullbackCongr (hsq₁ t₁ s₁)).app N₁ ≪≫ e₁) ⊗ᵢ
        ((Scheme.Modules.pullbackComp _ _).app N₂ ≪≫ (Scheme.Modules.pullbackCongr (hsq₂ t₁ s₁)).app N₂ ≪≫ f₁))) ≪≫
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm

theorem IsAlgEquivZero.of_tensor_iso_unit {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    {L M : A.Modules} (hL : IsAlgEquivZero a L) (e : L ⊗ M ≅ 𝟙_ A.Modules) : IsAlgEquivZero a M := by
  obtain ⟨T', h, hft, hgi, N, hN, t₀, t₁, ⟨e₀⟩, ⟨e₁⟩⟩ := hL

  obtain ⟨N', hN', ⟨eN⟩⟩ := hN.exists_tensor_inverse

  have uniq : ∀ {V : Scheme.{u}} (X Y Y' : V.Modules), (X ⊗ Y ≅ 𝟙_ _) → (X ⊗ Y' ≅ 𝟙_ _) → (Y ≅ Y') :=
    fun X Y Y' i i' =>
      (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫
        (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'
  refine ⟨T', h, hft, hgi, N', hN', t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  ·
    have i : (Scheme.Modules.pullback (baseChangeSnd a t₀)).obj N ⊗
        (Scheme.Modules.pullback (baseChangeSnd a t₀)).obj N' ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso eN ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
    exact uniq _ _ _ i ((e₀ ⊗ᵢ Iso.refl _) ≪≫ λ_ _)
  ·
    have i : (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N ⊗
        (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N' ≅ 𝟙_ _ :=
      (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso eN ≪≫
        Scheme.Modules.pullbackTensorUnitObjIso _
    have i' : (Scheme.Modules.pullback (baseChangeSnd a t₁)).obj N ⊗
        (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj M ≅ 𝟙_ _ :=
      (e₁ ⊗ᵢ Iso.refl _) ≪≫ (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫
        (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _
    exact uniq _ _ _ i i'

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

theorem FibrewiseAlgEquivZero.tensor {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L M : RigidifiedLineBundle c ε t} (hL : FibrewiseAlgEquivZero L) (hM : FibrewiseAlgEquivZero M) :
    FibrewiseAlgEquivZero (L.tensor M) := by
  intro k _ _ s
  exact IsAlgEquivZero.of_iso (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ((hL k s).tensor (hM k s))

theorem FibrewiseAlgEquivZero.of_tensor_iso_unit {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {L M : RigidifiedLineBundle c ε t}
    (e : Nonempty ((L.tensor M).L ≅ (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L))
    (hL : FibrewiseAlgEquivZero L) : FibrewiseAlgEquivZero M := by
  intro k _ _ s

  refine (hL k s).of_tensor_iso_unit ?_
  exact (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso e.some ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso _

def algEquivZeroGroupCut (c : C ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicGroupCondition c ε where
  toSubPicCondition := algEquivZeroCut c ε
  tensor_mem := fun _ _ _ hL hM => FibrewiseAlgEquivZero.tensor hL hM
  inv_mem := fun _ _ _ e hL => FibrewiseAlgEquivZero.of_tensor_iso_unit e hL

@[simp] theorem algEquivZeroGroupCut_toSubPicCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    (algEquivZeroGroupCut c ε).toSubPicCondition = algEquivZeroCut c ε := rfl

end AlgebraicGeometry.RelPicard

end
