import Mathlib
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Def.AlgebraicGeometry_SquareZeroDeformation
import Lemma.AlgebraicGeometry.SquareZeroRelTangent
import Def.AlgebraicGeometry_SmallExtensionPairTangent
import Abbrev.AlgebraicGeometry_TangentCoordsOfPair

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct IsLocalRing NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry

namespace RelTangentPoints

variable {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k x)
  (V : Type u) [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
  {Z₀ Z : Scheme.{u}} (f₀ : Z₀ ⟶ Spec (CommRingCat.of k))
  (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec k V) (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase k V))


theorem zeroSection_base : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ base V q₂ = f₀ := by
  rw [base, SquareZero.zeroSection_snd_assoc, SquareZero.basePoint_toBase, Category.comp_id]

theorem fst_zeroSection_base : (q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ) ≫ base V q₂ = base V q₂ := by
  rw [Category.assoc, zeroSection_base]; exact hZ.w

def translate (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = base V q₂) :
    RelTangentPoints x (L.one (𝟙 (Spec (CommRingCat.of k)))).1 V f₀ q₁ q₂ hZ :=
  ⟨(L.mul (base V q₂)
      (L.inv (base V q₂) ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
        rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]; exact fst_zeroSection_base V f₀ q₁ q₂ hZ⟩)
      ⟨w₀, hw₀⟩).1, by
    constructor
    · exact (L.mul (base V q₂) _ _).2
    ·
      have hψ : SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ base V q₂ = f₀ := zeroSection_base V f₀ q₁ q₂ hZ
      set A : SchemeHomOver (base V q₂) x := ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
          rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]; exact fst_zeroSection_base V f₀ q₁ q₂ hZ⟩ with hA
      set W : SchemeHomOver (base V q₂) x := ⟨w₀, hw₀⟩ with hW
      have hsame : schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A
          = schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ W := by
        apply Subtype.ext
        simp only [schemeHomOverComp_coe, hA, hW]
        rw [← Category.assoc, ← Category.assoc, SquareZero.zeroSection_fst, Category.id_comp]

      have hprod : L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A))
          (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A) = L.one f₀ := by
        rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
      have hinvnat : schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A)
          = L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A) := by
        calc schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A)
            = L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A)) (L.one f₀) :=
              (L.mul_one f₀ _).symm
          _ = L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ (L.inv (base V q₂) A))
                (L.mul f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A)
                  (L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A))) := by
              rw [L.mul_inv_cancel]
          _ = L.mul f₀ (L.one f₀) (L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A)) := by
              rw [← L.mul_assoc, hprod]
          _ = L.inv f₀ (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ A) := L.one_mul f₀ _
      have h1 : (schemeHomOverComp (SquareZero.zeroSection V f₀ q₁ q₂ hZ) hψ
          (L.mul (base V q₂) (L.inv (base V q₂) A) W)).1 = (L.one f₀).1 := by
        rw [L.mul_natural, hinvnat, hsame, L.inv_mul_cancel]
      have h2 : (L.one f₀).1 = f₀ ≫ (L.one (𝟙 (Spec (CommRingCat.of k)))).1 := by
        have := L.one_natural (𝟙 (Spec (CommRingCat.of k))) f₀ f₀ (Category.comp_id f₀)
        rw [← this, schemeHomOverComp_coe]
      rw [← h2, ← h1, schemeHomOverComp_coe]⟩

@[simp] theorem translate_coe (w₀ : Z ⟶ X) (hw₀ : w₀ ≫ x = base V q₂) :
    (translate x L V f₀ q₁ q₂ hZ w₀ hw₀).1 =
      (L.mul (base V q₂)
        (L.inv (base V q₂) ⟨q₁ ≫ SquareZero.zeroSection V f₀ q₁ q₂ hZ ≫ w₀, by
          rw [Category.assoc, Category.assoc, hw₀, ← Category.assoc]; exact fst_zeroSection_base V f₀ q₁ q₂ hZ⟩)
        ⟨w₀, hw₀⟩).1 := rfl

end RelTangentPoints

namespace SmallExtension

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
  (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
  [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
  (ι : V →ₗ[T'] T')
  (C : Type u) [CommRing C] [Algebra T' C]

variable (T') in


theorem thickening_isPullback :
    IsPullback (thickeningFst T' V C) (thickeningSnd T' V C) (reductionBase T' C) (SquareZero.toBase (ResidueField T') V) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (ResidueField T') (ResidueField T' ⊗[T'] C) (TrivSqZeroExt (ResidueField T') V))

def IsTangentCoordsOfPair {Y : Scheme.{u}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y)
    (γ : letI : Algebra (ResidueField T')
          (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) :=
        ((Ak.presheaf.germ ⊤ ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T'))) trivial).hom.comp
          (xk.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom)).toAlgebra
      ∀ (W : Type u) [AddCommGroup W] [Module (ResidueField T') W] [Module (ResidueField T')ᵐᵒᵖ W]
        [IsCentralScalar (ResidueField T') W] [Module.Finite (ResidueField T') W]
        {Z₀ Z : Scheme.{u}} [IsAffine Z₀] (f₀ : Z₀ ⟶ Spec (CommRingCat.of (ResidueField T')))
        (q₁ : Z ⟶ Z₀) (q₂ : Z ⟶ SquareZero.spec (ResidueField T') W)
        (hZ : IsPullback q₁ q₂ f₀ (SquareZero.toBase (ResidueField T') W)),
        letI : Module (ResidueField T') Γ(Z₀, ⊤) :=
          ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv ≫ f₀.appTop).hom.toAlgebra.toModule
        RelTangentPoints xk (Lk.one (𝟙 _)).1 W f₀ q₁ q₂ hZ ≃
          (IsLocalRing.CotangentSpace (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) →ₗ[ResidueField T']
            (Module.Dual (ResidueField T') W →ₗ[ResidueField T'] Γ(Z₀, ⊤))))
    [Module.Finite (ResidueField T') V]
    (c : letI : Algebra (ResidueField T')
          (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) :=
        ((Ak.presheaf.germ ⊤ ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T'))) trivial).hom.comp
          (xk.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv.hom)).toAlgebra
      letI : Module (ResidueField T') Γ(Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)), ⊤) :=
        ((Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).inv ≫ (reductionBase T' C).appTop).hom.toAlgebra.toModule
      IsLocalRing.CotangentSpace (Ak.presheaf.stalk ((Lk.one (𝟙 _)).1.base (IsLocalRing.closedPoint (ResidueField T')))) →ₗ[ResidueField T']
        (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] Γ(Spec (CommRingCat.of (ResidueField T' ⊗[T'] C)), ⊤))) : Prop :=
  ∃ (w₀ : Spec (CommRingCat.of (thickening T' V C)) ⟶ Ak)
    (hw₀ : w₀ ≫ xk = RelTangentPoints.base V (thickeningSnd T' V C)),
    IsTangentOfPair I V ι C u v (w₀ ≫ ak) ∧
    c = γ V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C) (thickening_isPullback V C)
          (RelTangentPoints.translate xk Lk V (reductionBase T' C) (thickeningFst T' V C) (thickeningSnd T' V C)
            (thickening_isPullback V C) w₀ hw₀)

end SmallExtension

end AlgebraicGeometry

end
