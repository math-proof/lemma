import Mathlib
import Lemma.Definitions.Def_ModularCurve_DRModelPackage
import Lemma.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Lemma.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Lemma.Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Lemma.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Lemma.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Lemma.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Lemma.Definitions.Def_AlgebraicCurve_CurveModel
import Lemma.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Lemma.Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Lemma.Definitions.Def_JacJ1Iface
import Lemma.Definitions.Def_SheafOfModules_Monoidal

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

variable (p : ℕ) [Fact p.Prime]

variable {p} in

structure DRModelPackage.LegTwoInput (𝔛 : DRModelPackage p) where

  𝒱 : (DRModel p).TwoAffineOpenCover
  hH0 : ∀ (A : Type) [CommRing A] [Algebra ℤ A],
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd (DRModel.toBase p) (Scheme.TwoAffineOpenCover.specMap ℤ A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback (DRModel.toBase p) (Scheme.TwoAffineOpenCover.specMap ℤ A), ⊤))
  hcov : ∀ (V : (Spec (CommRingCat.of ℤ)).affineOpens) (F : Finset ↥𝔛.smoothLocus),
    (∀ x ∈ F, (𝔛.smoothLocus.ι ≫ (DRModel.toBase p)).base x ∈ (V : (Spec (CommRingCat.of ℤ)).Opens)) →
    ∃ W : (𝔛.smoothLocus : Scheme.{0}).Opens, IsAffineOpen W ∧
      W ≤ (𝔛.smoothLocus.ι ≫ (DRModel.toBase p)) ⁻¹ᵁ (V : (Spec (CommRingCat.of ℤ)).Opens) ∧ ∀ x ∈ F, x ∈ W
  hfib : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ))
    (L : (pullback (DRModel.toBase p) x).Modules), Scheme.Modules.IsInvertible L →
    IsAlgEquivZero (pullback.snd (DRModel.toBase p) x) L →
    ∀ s : 𝟙_ (pullback (DRModel.toBase p) x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback (DRModel.toBase p) x).Modules)
  hgred : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)), IsReduced (pullback (DRModel.toBase p) x)

  genus : ℕ
  hg : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ))
    (𝒲 : (pullback (pullback.snd (DRModel.toBase p) (𝟙 (Spec (CommRingCat.of ℤ)))) x).TwoAffineOpenCover),
    Module.finrank k (𝒲.sectionsOf (fibreAt (DRModel.toBase p) (𝟙 _) x)
      (SheafOfModules.unit (pullback (pullback.snd (DRModel.toBase p) (𝟙 (Spec (CommRingCat.of ℤ)))) x).ringCatSheaf)).H1 = genus
  hpool : ∀ (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ), ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)))
  hbad : ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
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
      (∃ W₁ : (pullback (DRModel.toBase p) s).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) s)) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))

end ModularCurve

end
