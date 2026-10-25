import Mathlib
import Structure.ModularCurve_X0
import Instance.ModularCurve_IgusaScheme
import Instance.AlgebraicCurve_TwoChartIntegralModel
import Structure.AlgebraicCurve_CurveModel
import Instance.ModularCurve_GeometricBaseChange
import Instance.ModularCurve_ArithmeticGalois
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Def.ModularCurve_SupersingularModuli
import Structure.AlgebraicGeometry_TwoAffineOpenCover

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

variable (p : ℕ) [Fact p.Prime]

theorem DRModelPackage.neZero_of_fact_prime : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

attribute [local instance] DRModelPackage.neZero_of_fact_prime

open ModularCurve.IgusaScheme

abbrev DRModel : Scheme.{0} :=
  AlgebraicCurve.TwoChartIntegralModel ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

abbrev DRModel.toBase : DRModel p ⟶ Spec (CommRingCat.of ℤ) :=
  AlgebraicCurve.TwoChartIntegralModel.toBase ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

abbrev DRModel.pFibre : Scheme.{0} :=
  AlgebraicCurve.TwoChartIntegralModel.fibre ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (Ideal.span {(p : ℤ)})

def DRModel.sectionFibre (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p))
    {κ : Type} [CommRing κ] (a : ℤ →+* κ) :
    Spec (CommRingCat.of κ) ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom a)) :=
  pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ε.1) (𝟙 _)
    (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])

structure DRModelPackage where

  isProper : IsProper (DRModel.toBase p)
  flat : Flat (DRModel.toBase p)
  isIntegral : IsIntegral (DRModel p)

  normal : ∀ U : (DRModel p).Opens, IsAffineOpen U → IsIntegrallyClosed Γ(DRModel p, U)

  M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p)
  e₀ : M₀.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
  [e₀_iso : IsIso e₀]
  he₀ : e₀ ≫ pullback.snd _ _ = M₀.toBase
  Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p)
  eη : Mη.C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
  [eη_iso : IsIso eη]
  heη : eη ≫ pullback.snd _ _ = Mη.toBase
  hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eη ≫ pullback.fst _ _ →
      Mη.pointEquivPlace x' = arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x
  hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst (DRModel.toBase p) _ = x.1 ≫ eη ≫ pullback.fst (DRModel.toBase p) _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring)

  εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)
  εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℤ))) (DRModel.toBase p)

  smoothLocus : (DRModel p).Opens

  [smoothLocus_relDim : SmoothOfRelativeDimension 1 (smoothLocus.ι ≫ DRModel.toBase p)]
  smoothLocus_maximal : ∀ U : (DRModel p).Opens, Smooth (U.ι ≫ DRModel.toBase p) → U ≤ smoothLocus
  εinf_mem_smoothLocus : Set.range εinf.1.base ⊆ (smoothLocus : Set (DRModel p))
  εzero_mem_smoothLocus : Set.range εzero.1.base ⊆ (smoothLocus : Set (DRModel p))
  smooth_away : Smooth (pullback.snd (DRModel.toBase p)
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (p : ℤ))))))

  pFibre_reduced : IsReduced (DRModel.pFibre p)

  ratModel : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ], CurveModel κ (RatFunc κ)

  compInf : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      (ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
  compZero : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      (ratModel κ).C ⟶ pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ)))
  compInf_over : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ], compInf κ ≫ pullback.snd _ _ = (ratModel κ).toBase
  compZero_over : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ], compZero κ ≫ pullback.snd _ _ = (ratModel κ).toBase
  compInf_isClosedImmersion : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ], IsClosedImmersion (compInf κ)
  compZero_isClosedImmersion : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ], IsClosedImmersion (compZero κ)
  comp_jointly_surjective : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
      (x : ↥(pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))))),
      x ∈ Set.range (compInf κ).base ∨ x ∈ Set.range (compZero κ).base

  range_compInf_ne : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      Set.range (compInf κ).base ≠ Set.range (compZero κ).base

  crossing_reduced : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ], IsReduced (pullback (compInf κ) (compZero κ))

  crossing_card : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ],
      Nat.card ↥(pullback (compInf κ) (compZero κ)) = Nat.card ↥(ssJSet p κ)

  εinf_mem_compInf : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      Set.range (DRModel.sectionFibre (p := p) εinf (algebraMap ℤ κ)).base ⊆ Set.range (compInf κ).base
  εzero_mem_compZero : ∀ (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ],
      Set.range (DRModel.sectionFibre (p := p) εzero (algebraMap ℤ κ)).base ⊆ Set.range (compZero κ).base

  w : DRModel p ≅ DRModel p
  w_over : w.hom ≫ DRModel.toBase p = DRModel.toBase p
  w_invol : w.hom ≫ w.hom = 𝟙 _

  w_sections : εinf.1 ≫ w.hom = εzero.1

  chartFin_finite : letI := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).toRingHom.toAlgebra
    Module.Finite (Polynomial ℤ) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))
  chartInf_finite : letI := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).toRingHom.toAlgebra
    Module.Finite (Polynomial ℤ) ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))

attribute [instance] DRModelPackage.e₀_iso DRModelPackage.eη_iso DRModelPackage.smoothLocus_relDim

end ModularCurve

end
