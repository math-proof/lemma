import Lemma.Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Lemma.Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option autoImplicit false

open IsDedekindDomain NumberField EisensteinWeightOne CongruenceSubgroup

noncomputable section

namespace AutomorphicForm

def viaGeneralCuspNotion : CuspidalityNotion (ℤ√(-2)) where
  IsCusp := fun F _i1 _i2 Φ =>
    (∃ R : SmoothCuspRealizationAt F (productionPinsGeneral F)
        ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
      IsGenuineCuspRealizationAt F (productionPinsGeneral F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral) R ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
      (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
        IsArchHolomorphicAt w hw R.toFun)) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))

theorem viaGeneralCuspNotion_isCusp_iff {F : Type} [Field F] [NumberField F]
    (Φ : HeckeEigensystem F (ℤ√(-2))) :
    viaGeneralCuspNotion.IsCusp F Φ ↔
      (∃ R : SmoothCuspRealizationAt F (productionPinsGeneral F)
          ((Φ.map iotaZsqrtdNegTwo).toRawCentral),
        IsGenuineCuspRealizationAt F (productionPinsGeneral F)
            ((Φ.map iotaZsqrtdNegTwo).toRawCentral) R ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          IsArchHolomorphicAt w hw R.toFun)) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
        Φ.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))) :=
  Iff.rfl

theorem isArithGenuineCuspRealizableVia_of_viaGeneralCuspNotion {F : Type} [Field F]
    [NumberField F] (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaGeneralCuspNotion.IsCusp F Φ) :
    IsArithGenuineCuspRealizableVia F (productionPinsGeneral F) iotaZsqrtdNegTwo Φ :=
  ⟨h.1.choose, h.1.choose_spec.1⟩

open MeasureTheory in

theorem not_ae_eq_zero_of_isGenuineCuspRealizationAt {F : Type} [Field F] [NumberField F]
    {Φ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F (productionPinsGeneral F) Φ)
    (hR : IsGenuineCuspRealizationAt F (productionPinsGeneral F) Φ R) :
    ¬ (∀ᵐ g ∂(productionPinsGeneral F).μ, R.toFun g = 0) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := (productionPinsGeneral F).mS
  haveI : Measure.IsHaarMeasure (productionPinsGeneral F).μ :=
    isHaarMeasure_productionPinsOf_μ F _ _ _ _
  intro hae
  obtain ⟨g, hg⟩ := R.exists_ne_zero
  exact hg (congrFun (Measure.eq_of_ae_eq hae hR continuous_const) g)

theorem viaCompactCuspNotion_isCusp_of_viaGeneralCuspNotion {F : Type} [Field F]
    [NumberField F] (hodd : Odd (classNumber F)) (Φ : HeckeEigensystem F (ℤ√(-2)))
    (h : viaGeneralCuspNotion.IsCusp F Φ) :
    viaCompactCuspNotion.IsCusp F Φ := by
  obtain ⟨hR, hS⟩ := h
  rw [productionPinsGeneral_eq_compact_of_odd F hodd] at hR
  obtain ⟨R, _, harch, hhol⟩ := hR
  exact ⟨⟨R, harch, hhol⟩, hS⟩

end AutomorphicForm

end
