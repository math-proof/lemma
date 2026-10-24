import Mathlib
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

namespace AlgebraicGeometry.TwoGluedCurves

variable {κ : Type u} [Field κ]
  {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  {c₁ : C₁ ⟶ Spec (.of κ)} {c₂ : C₂ ⟶ Spec (.of κ)}
  (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x)
  {ι : Type v} (p₁ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₁) (p₂ : ι → SchemeHomOver (𝟙 (Spec (.of κ))) c₂)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

def nodeSectionFst (j : ι) : T ⟶ pullback c₁ h :=
  rigSection c₁ h (p₁ j)

def nodeSectionSnd (j : ι) : T ⟶ pullback c₂ h :=
  rigSection c₂ h (p₂ j)

def nodeLocus (j : ι) (W : (pullback x h).Opens) : T.Opens :=
  (nodeSectionFst p₁ h j) ⁻¹ᵁ ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W) ⊓
    (nodeSectionSnd p₂ h j) ⁻¹ᵁ ((curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)

def NodeCondition (u : ι → Γ(T, ⊤)ˣ) (W : (pullback x h).Opens) (j : ι)
    (f : Γ(pullback c₁ h, (curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W))
    (g : Γ(pullback c₂ h, (curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)) : Prop :=
  (nodeSectionFst p₁ h j).appLE ((curveChange i₁.1 i₁.2 h) ⁻¹ᵁ W)
      (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_left f =
    T.presheaf.map (homOfLE le_top).op (u j : Γ(T, ⊤)) *
      (nodeSectionSnd p₂ h j).appLE ((curveChange i₂.1 i₂.2 h) ⁻¹ᵁ W)
        (nodeLocus x i₁ i₂ p₁ p₂ h j W) inf_le_right g

def IsNodeUnitModule (u : ι → Γ(T, ⊤)ˣ) (M : (pullback x h).Modules) : Prop :=
  ∃ (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁.1 i₁.2 h)).obj
      (SheafOfModules.unit (pullback c₁ h).ringCatSheaf))
    (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂.1 i₂.2 h)).obj
      (SheafOfModules.unit (pullback c₂ h).ringCatSheaf)),
    ∀ W : (pullback x h).Opens,
      Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
      Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
        {fg | ∀ j : ι, NodeCondition x i₁ i₂ p₁ p₂ h u W j fg.1 fg.2}

end AlgebraicGeometry.TwoGluedCurves

end
