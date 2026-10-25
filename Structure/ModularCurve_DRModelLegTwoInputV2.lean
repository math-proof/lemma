import Mathlib
import Abbrev.ModularCurve_DRModelPackage
import Structure.ModularCurve_DRModelLegTwoInput
import Instance.AlgebraicGeometry_RelativePicardFunctor
import Structure.AlgebraicGeometry_RepresentsRelSubPic
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Def.AlgebraicGeometry_RelPicardChartSections
import Instance.AlgebraicGeometry_SmoothProperCurveBase
import Structure.AlgebraicGeometry_TwoAffineOpenCover
import Lemma.AlgebraicGeometry.TwoChartCechSectionsOf
import Structure.AlgebraicCurve_CurveModel
import Instance.AlgebraicCurve_RatFuncPlaces
import Lemma.AlgebraicCurve.RatFuncPlaceInfty
import Structure.JacJ1Iface
import Instance.SheafOfModules_Monoidal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

variable {p : ℕ} [Fact p.Prime]

structure DRModelPackage.LegTwoInputV2 (𝔛 : DRModelPackage p) extends 𝔛.LegTwoInput where
  hbadV5 : ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)), ¬ Smooth (pullback.snd (DRModel.toBase p) s) →
    ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback (DRModel.toBase p) s) (i₂ : M₂.C ⟶ pullback (DRModel.toBase p) s)
      (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
      (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback (DRModel.toBase p) s).TwoAffineOpenCover),
      i₁ ≫ pullback.snd (DRModel.toBase p) s = M₁.toBase ∧ i₂ ≫ pullback.snd (DRModel.toBase p) s = M₂.toBase ∧
      Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
      Function.Injective a ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (P₁ : M₁.C) (Q₂ : M₂.C), i₁.base P₁ = i₂.base Q₂ →
        ∃ i, P₁ = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          Q₂ = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      IsReduced (pullback i₁ i₂) ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k) ∧
      Set.range i₁.base ∩ ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) : Set ↥(pullback (DRModel.toBase p) s)) =
        connectedComponentIn ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) : Set ↥(pullback (DRModel.toBase p) s)) (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
        (pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens)) ∧
      (∀ y : ↥(pullback (DRModel.toBase p) s),
        (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
          y ∈ (pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens)) ∧
      (∃ W₁ : (pullback (DRModel.toBase p) s).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) s)) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))

end ModularCurve

end
