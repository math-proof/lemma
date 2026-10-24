import Mathlib
import Lemma.Definitions.Def_AlgebraicCurve_CurveModel
import Lemma.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
  NeronModelInfra

namespace AlgebraicGeometry.TwoGluedProjectiveLines

variable {κ : Type u} [Field κ] [IsAlgClosed κ]
  {X : Scheme.{u}} (x : X ⟶ Spec (.of κ))
  (M₁ M₂ : CurveModel κ (RatFunc κ)) (i₁ : M₁.C ⟶ X) (i₂ : M₂.C ⟶ X)
  (hi₁ : i₁ ≫ x = M₁.toBase) (hi₂ : i₂ ≫ x = M₂.toBase)
  {s : ℕ} (a b : Fin s → κˣ)
  {T : Scheme.{u}} (h : T ⟶ Spec (.of κ))

def pointAt (M : CurveModel κ (RatFunc κ)) (c : κ) : SchemeHomOver (𝟙 (Spec (.of κ))) M.toBase :=
  M.pointEquivPlace.symm (RationalFunctionField.placeOfPoint κ c)

def nodeSectionFst (i : Fin s) : T ⟶ pullback M₁.toBase h :=
  rigSection M₁.toBase h (pointAt M₁ (a i : κ))

def nodeSectionSnd (i : Fin s) : T ⟶ pullback M₂.toBase h :=
  rigSection M₂.toBase h (pointAt M₂ (b i : κ))

def nodeLocus (i : Fin s) (W : (pullback x h).Opens) : T.Opens :=
  (nodeSectionFst M₁ a h i) ⁻¹ᵁ ((curveChange i₁ hi₁ h) ⁻¹ᵁ W) ⊓
    (nodeSectionSnd M₂ b h i) ⁻¹ᵁ ((curveChange i₂ hi₂ h) ⁻¹ᵁ W)

def NodeCondition (u : Fin s → Γ(T, ⊤)ˣ) (W : (pullback x h).Opens) (i : Fin s)
    (f : Γ(pullback M₁.toBase h, (curveChange i₁ hi₁ h) ⁻¹ᵁ W))
    (g : Γ(pullback M₂.toBase h, (curveChange i₂ hi₂ h) ⁻¹ᵁ W)) : Prop :=
  (nodeSectionFst M₁ a h i).appLE ((curveChange i₁ hi₁ h) ⁻¹ᵁ W)
      (nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W) inf_le_left f =
    T.presheaf.map (homOfLE le_top).op (u i : Γ(T, ⊤)) *
      (nodeSectionSnd M₂ b h i).appLE ((curveChange i₂ hi₂ h) ⁻¹ᵁ W)
        (nodeLocus x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h i W) inf_le_right g

def IsNodeUnitModule (u : Fin s → Γ(T, ⊤)ˣ) (M : (pullback x h).Modules) : Prop :=
  ∃ (j₁ : M ⟶ (Scheme.Modules.pushforward (curveChange i₁ hi₁ h)).obj
      (SheafOfModules.unit (pullback M₁.toBase h).ringCatSheaf))
    (j₂ : M ⟶ (Scheme.Modules.pushforward (curveChange i₂ hi₂ h)).obj
      (SheafOfModules.unit (pullback M₂.toBase h).ringCatSheaf)),
    ∀ W : (pullback x h).Opens,
      Function.Injective (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) ∧
      Set.range (fun m : Γ(M, W) => (j₁.app W m, j₂.app W m)) =
        {fg | ∀ i : Fin s, NodeCondition x M₁ M₂ i₁ i₂ hi₁ hi₂ a b h u W i fg.1 fg.2}

end AlgebraicGeometry.TwoGluedProjectiveLines

end
