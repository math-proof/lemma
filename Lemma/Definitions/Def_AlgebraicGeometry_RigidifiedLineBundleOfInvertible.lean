import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Lemma.Definitions.Def_SheafOfModules_Monoidal
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {V : Scheme.{u}}

def isoOfTensorIsoUnit (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _) (i' : X ⊗ Y' ≅ 𝟙_ _) : Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫ (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

def tensorTensorTensorComm (W X Y Z : V.Modules) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ _ _ _ ≪≫ (Iso.refl W ⊗ᵢ ((α_ _ _ _).symm ≪≫ (β_ X Y ⊗ᵢ Iso.refl Z) ≪≫ α_ _ _ _)) ≪≫ (α_ _ _ _).symm

theorem nonempty_dual_tensorUnit_iso (V : Scheme.{u}) : Nonempty (dual (𝟙_ V.Modules) ≅ 𝟙_ V.Modules) :=
  ⟨(λ_ _).symm ≪≫ (isInvertible_unit V).dual.2.some⟩

end Scheme.Modules

namespace RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}}
  {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}

@[reassoc (attr := simp)]
theorem rigSection_snd (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R)) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem baseChangeSnd_snd (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 :=
  pullback.lift_snd _ _ _

abbrev rigCorrection (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (L : (Limits.pullback c t).Modules) : T.Modules :=
  Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

def rigSectionPullbackSndPullbackIso (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (D : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj D) ≅ D :=
  (Scheme.Modules.pullbackComp _ _).app D ≪≫ (Scheme.Modules.pullbackCongr (rigSection_snd ε t)).app D ≪≫
    (Scheme.Modules.pullbackId _).app D

def RigidifiedLineBundle.ofInvertible (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle c ε t where
  L := Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t) L
  isInvertible := hL.tensor (((hL.pullback _).dual).1.pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ rigSectionPullbackSndPullbackIso ε t _) ≪≫ (hL.pullback _).dual.2.some⟩

@[simp] theorem RigidifiedLineBundle.ofInvertible_L (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L = Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t) L := rfl

theorem RigidifiedLineBundle.ofInvertible_L_eq_tensor (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L =
      L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (rigCorrection ε t L) := rfl

namespace RigidifiedLineBundle

theorem nonempty_ofInvertible_iso_of_iso {L L' : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') (e : L ≅ L') :
    Nonempty ((ofInvertible (ε := ε) L hL).L ≅ (ofInvertible (ε := ε) L' hL').L) := by
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ e⟩

theorem nonempty_ofInvertible_iso_of_rigidified (M : RigidifiedLineBundle c ε t) :
    Nonempty ((ofInvertible (ε := ε) M.L M.isInvertible).L ≅ M.L) := by
  let d := Scheme.Modules.dualMapIso M.rigidified.some
  obtain ⟨u⟩ := Scheme.Modules.nonempty_dual_tensorUnit_iso T
  exact ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d ≪≫ u) ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)) ≪≫
    ρ_ M.L⟩

theorem nonempty_ofInvertible_tensor_iso {L L' : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') :
    Nonempty ((ofInvertible (ε := ε) (L ⊗ L') (hL.tensor hL')).L ≅
      ((ofInvertible (ε := ε) L hL).tensor (ofInvertible (ε := ε) L' hL')).L) := by
  have hεL := hL.pullback (rigSection c t ε)
  have hεL' := hL'.pullback (rigSection c t ε)

  let d₁ := Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso (rigSection c t ε) L L')
  obtain ⟨d₂⟩ := hεL.dual_tensor hεL'
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)) ≪≫
    Scheme.Modules.tensorTensorTensorComm _ _ _ _⟩

theorem nonempty_ofInvertible_pullbackSnd_tensor_iso {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((ofInvertible (ε := ε) ((Scheme.Modules.pullback (pullback.snd c t)).obj N ⊗ L) ((hN.pullback _).tensor hL)).L ≅
      (ofInvertible (ε := ε) L hL).L) := by
  have hεL := hL.pullback (rigSection c t ε)

  let d₁ := Scheme.Modules.dualMapIso
    (Scheme.Modules.pullbackTensorObjIso (rigSection c t ε) _ L ≪≫ (rigSectionPullbackSndPullbackIso ε t N ⊗ᵢ Iso.refl _))
  obtain ⟨d₂⟩ := hN.dual_tensor hεL
  obtain ⟨p⟩ := hN.dual.2
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)) ≪≫
    Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫
    (((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso p ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _) ⊗ᵢ Iso.refl _) ≪≫ λ_ _⟩

theorem nonempty_ofInvertible_pullbackAlong_iso (ψ : SchemeHomOver t' t) {L : (Limits.pullback c t).Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (((ofInvertible (ε := ε) L hL).pullbackAlong ψ).L ≅
      (ofInvertible (ε := ε) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) (hL.pullback _)).L) := by
  have hεL := hL.pullback (rigSection c t ε)

  obtain ⟨d₁⟩ := hεL.pullback_dual ψ.1
  let d₂ := Scheme.Modules.dualMapIso
    ((Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).app L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_)⟩

  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (baseChangeSnd_snd ψ)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ (Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂)

end RigidifiedLineBundle

end RelPicard

end AlgebraicGeometry

end
