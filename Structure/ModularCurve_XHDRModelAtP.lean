import Mathlib
import Instance.ModularCurve_XHDifferentialsModL
import Def.ModularCurve_XHOperators
import Abbrev.ModularCurve_IgusaScheme
import Instance.AlgebraicCurve_TwoChartIntegralModel
import Structure.AlgebraicCurve_CurveModel
import Structure.AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Abbrev.ModularCurve_XHDRModelAtP
import Instance.ModularCurve_XHDRModelAtP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
open scoped MatrixGroups

namespace ModularCurve

namespace XHDRLevel


variable (p : ℕ) (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))


abbrev toBase : X p Γ hj ⟶ Spec (CommRingCat.of (R p)) :=
  TwoChartIntegralModel.toBase (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

abbrev chartAlgFin := TwoChartIntegralModel.chartAlgFin (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)
abbrev chartAlgInf := TwoChartIntegralModel.chartAlgInf (R p) ↥(qExpFunctionFieldC ℚ Γ) (jAt Γ hj)

variable {p Γ hj}


def sectionFibre (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p Γ hj))
    {κ : Type} [CommRing κ] (toκ : R p →+* κ) : Spec (CommRingCat.of κ) ⟶ fibre (Γ := Γ) (hj := hj) toκ :=
  pullback.lift (Spec.map (CommRingCat.ofHom toκ) ≫ ε.1) (𝟙 _)
    (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])


def overOfIso (w : X p Γ hj ≅ X p Γ hj) (hw : w.hom ≫ toBase p Γ hj = toBase p Γ hj) :
    SchemeHomOver (toBase p Γ hj) (toBase p Γ hj) := ⟨w.hom, hw⟩

end XHDRLevel

open XHDRLevel

section

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
  (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))


structure XHDRModelAtP where

  [isProper : IsProper (toBase p (ΓM M H) hj)]
  [flat : Flat (toBase p (ΓM M H) hj)]
  [isIntegral : IsIntegral (X p (ΓM M H) hj)]
  [lfp : LocallyOfFinitePresentation (toBase p (ΓM M H) hj)]

  normal : ∀ U : (X p (ΓM M H) hj).Opens, IsAffineOpen U → IsIntegrallyClosed Γ(X p (ΓM M H) hj, U)

  [isProper0 : IsProper (toBase p (ΓN p M H hpM) hj)]
  [smooth0 : SmoothOfRelativeDimension 1 (toBase p (ΓN p M H hpM) hj)]

  Meta : CurveModel (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)
  eeta : Meta.C ⟶ pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
  [eeta_iso : IsIso eeta]
  heeta : eeta ≫ pullback.snd _ _ = Meta.toBase

  hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta.C // s ≫ Meta.toBase = 𝟙 _}),
      x'.1 ≫ eeta ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ eeta ≫ pullback.fst _ _ →
      Meta.pointEquivPlace x' = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) g • Meta.pointEquivPlace x

  [Meta_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eeta ≫ pullback.fst (toBase p (ΓM M H) hj)
      (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)))]
  Meta_pin : ∀ a : ↥(chartAlgFin p (ΓM M H) hj),
    ((Meta.ffEquiv.symm
        (Meta.C.germToFunctionField
          ((eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((ιFin p (ΓM M H) hj) ''ᵁ ⊤))
          (((eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).app
              ((ιFin p (ΓM M H) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓM M H) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓM M H) hj))).inv a))))
        : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((a : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ)

  smooth_generic : SmoothOfRelativeDimension 1
    (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))
  geomIntegral_generic : GeometricallyIntegral
    (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))))

  εinf : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)
  εzero : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase p (ΓM M H) hj)

  rhoInf : ↥(chartAlgInf p (ΓM M H) hj) →ₐ[R p] R p
  rhoInf_spec : ∀ b : ↥(chartAlgInf p (ΓM M H) hj),
    ((rhoInf b : R p) : ℚ) = ((b : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ).coeff 0
  εinf_chart : εinf.1 = Spec.map (CommRingCat.ofHom rhoInf.toRingHom) ≫ ιInf p (ΓM M H) hj

  w : X p (ΓM M H) hj ≅ X p (ΓM M H) hj
  w_over : w.hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj
  w_sections : εinf.1 ≫ w.hom = εzero.1

  dia : (ZMod M)ˣ → (X p (ΓM M H) hj ≅ X p (ΓM M H) hj)
  dia_over : ∀ d, (dia d).hom ≫ toBase p (ΓM M H) hj = toBase p (ΓM M H) hj
  dia_mul : ∀ d d', (dia (d * d')).hom = (dia d).hom ≫ (dia d').hom
  dia_mem : ∀ d, d ∈ H → dia d = Iso.refl _

  dia_generic : ∀ (d : (ZMod M)ˣ)
      (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta.C // s ≫ Meta.toBase = 𝟙 _}),
      x'.1 ≫ eeta ≫ pullback.fst _ _ = x.1 ≫ eeta ≫ pullback.fst _ _ ≫ (dia d).hom →
      Meta.pointEquivPlace x' = SemilinearAut.ofAlgAut (diamondAutHBar M H d) • Meta.pointEquivPlace x

  w_dia : ∀ d, w.hom ≫ (dia d).hom = (dia d).hom ≫ w.hom

  w_sq : ∀ d : (ZMod M)ˣ,
    ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) * (p : ZMod (M / p)) = 1 →
      w.hom ≫ w.hom = (dia d).hom

  π : SchemeHomOver (toBase p (ΓM M H) hj) (toBase p (ΓN p M H hpM) hj)
  iota0 : ↥(chartAlgFin p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj)
  iota0_spec : ∀ b, (((iota0 b : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
    ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
  pi_chart : ιFin p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iota0.toRingHom) ≫ ιFin p (ΓN p M H hpM) hj

  iotaInf : ↥(chartAlgInf p (ΓN p M H hpM) hj) →ₐ[R p] ↥(chartAlgInf p (ΓM M H) hj)
  iotaInf_spec : ∀ b, (((iotaInf b : ↥(chartAlgInf p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) =
    ((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)
  pi_chartInf : ιInf p (ΓM M H) hj ≫ π.1 = Spec.map (CommRingCat.ofHom iotaInf.toRingHom) ≫ ιInf p (ΓN p M H hpM) hj

  dia0 : (ZMod (M / p))ˣ → (X p (ΓN p M H hpM) hj ≅ X p (ΓN p M H hpM) hj)
  dia0_over : ∀ d, (dia0 d).hom ≫ toBase p (ΓN p M H hpM) hj = toBase p (ΓN p M H hpM) hj

  pi_dia : ∀ d : (ZMod M)ˣ, (dia d).hom ≫ π.1 = π.1 ≫ (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).hom

  smoothLocus : (X p (ΓM M H) hj).Opens
  [smoothLocus_relDim : SmoothOfRelativeDimension 1 (smoothLocus.ι ≫ toBase p (ΓM M H) hj)]
  smoothLocus_maximal : ∀ U : (X p (ΓM M H) hj).Opens, Smooth (U.ι ≫ toBase p (ΓM M H) hj) → U ≤ smoothLocus
  εinf_mem_smoothLocus : Set.range εinf.1.base ⊆ (smoothLocus : Set (X p (ΓM M H) hj))
  εzero_mem_smoothLocus : Set.range εzero.1.base ⊆ (smoothLocus : Set (X p (ΓM M H) hj))

  fibre_reduced : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    IsReduced (fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))

  Mfib : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    CurveModel (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))
  efib : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    (Mfib A hA ρ hρ).C ⟶ fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)
  efib_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)), IsIso (efib A hA ρ hρ)
  hefib : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    efib A hA ρ hρ ≫ pullback.snd _ _ = (Mfib A hA ρ hρ).toBase

  [Mfib_chart_nonempty : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Nonempty (Scheme.Opens.toScheme ((efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj)
      (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)))]
  Mfib_pin : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (b : ↥(chartAlgFin p (ΓN p M H hpM) hj)) (y : LaurentSeries ↥A),
    coeffMap A.subtype y = coeffEmb (AlgebraicClosure ℚ) (((b : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))) : LaurentSeries ℚ)) →
    (((Mfib A hA ρ hρ).ffEquiv.symm
        ((Mfib A hA ρ hρ).C.germToFunctionField
          ((efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))) ⁻¹ᵁ
            ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤))
          (((efib A hA ρ hρ ≫ pullback.fst (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).app
              ((ιFin p (ΓN p M H hpM) hj) ''ᵁ ⊤)).hom
            (((ιFin p (ΓN p M H hpM) hj).appIso ⊤).inv
              ((Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin p (ΓN p M H hpM) hj))).inv b))))
        : ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
      coeffMap (IsLocalRing.residue ↥A) y

  comp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Fin 2 → (fibre (Γ := ΓN p M H hpM) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
  comp_over : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
    comp A hA ρ hρ i ≫ pullback.snd _ _ = pullback.snd _ _
  comp_isClosedImmersion : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2),
    IsClosedImmersion (comp A hA ρ hρ i)
  comp_jointly_surjective : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (y : fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ)), y ∈ Set.range (comp A hA ρ hρ 0).base ∨ y ∈ Set.range (comp A hA ρ hρ 1).base
  range_comp_ne : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Set.range (comp A hA ρ hρ 0).base ≠ Set.range (comp A hA ρ hρ 1).base

  comp_pi : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    comp A hA ρ hρ 0 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ) = 𝟙 _

  comp1_pi_place : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (Mfib A hA ρ hρ).C),
    ∃ h : (inv (efib A hA ρ hρ)).base ((efib A hA ρ hρ ≫ comp A hA ρ hρ 1 ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base P.1) ∈ closedPoints (Mfib A hA ρ hρ).C,
      (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p ((Mfib A hA ρ hρ).placeOfPoint P)

  comp_w : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    comp A hA ρ hρ 0 ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) = comp A hA ρ hρ 1

  pi_w_comp0_place : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (P : closedPoints (Mfib A hA ρ hρ).C),
    ∃ h : (inv (efib A hA ρ hρ)).base ((efib A hA ρ hρ ≫ comp A hA ρ hρ 0 ≫ fibreMap (overOfIso w w_over) ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap π ((IsLocalRing.residue ↥A).comp ρ)).base P.1) ∈
        closedPoints (Mfib A hA ρ hρ).C,
      (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ = qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p ((Mfib A hA ρ hρ).placeOfPoint P)

  comp_dia : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) (i : Fin 2) (d : (ZMod M)ˣ),
    comp A hA ρ hρ i ≫ fibreMap (overOfIso (dia d) (dia_over d)) ((IsLocalRing.residue ↥A).comp ρ) =
      fibreMap (overOfIso (dia0 (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)) (dia0_over _)) ((IsLocalRing.residue ↥A).comp ρ) ≫ comp A hA ρ hρ i

  εinf_mem_comp0 : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Set.range (sectionFibre εinf ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp A hA ρ hρ 0).base
  εzero_mem_comp1 : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    Set.range (sectionFibre εzero ((IsLocalRing.residue ↥A).comp ρ)).base ⊆ Set.range (comp A hA ρ hρ 1).base

  crossing_reduced : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    IsReduced (pullback (comp A hA ρ hρ 0) (comp A hA ρ hρ 1))
  nodeEquiv : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)),
    ↥(pullback (comp A hA ρ hρ 0) (comp A hA ρ hρ 1)) ≃ ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)

  node_pin : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (n : ↥(pullback (comp A hA ρ hρ 0) (comp A hA ρ hρ 1))),
    (∃ h : (inv (efib A hA ρ hρ)).base ((pullback.snd (comp A hA ρ hρ 0) (comp A hA ρ hρ 1)).base n) ∈ closedPoints (Mfib A hA ρ hρ).C,
        (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          ((nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM)))) ∧
    (∃ h : (inv (efib A hA ρ hρ)).base ((pullback.fst (comp A hA ρ hρ 0) (comp A hA ρ hρ 1)).base n) ∈ closedPoints (Mfib A hA ρ hρ).C,
        (Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          qExpFrobeniusPlaceModL (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p
            ((nodeEquiv A hA ρ hρ n : ↥(ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p)) : Place (IsLocalRing.ResidueField ↥A) ↥(qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM))))

attribute [instance] XHDRModelAtP.eeta_iso XHDRModelAtP.smoothLocus_relDim
  XHDRModelAtP.efib_iso XHDRModelAtP.Mfib_chart_nonempty XHDRModelAtP.Meta_chart_nonempty

end

namespace XHDRModelAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))} (𝔛 : XHDRModelAtP p M H hpM hj)


end XHDRModelAtP

end ModularCurve

end
