import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Structure.LanglandsTunnell_CubicInduction_DataOn
import Def.LanglandsTunnell_CubicInduction_DataOn
set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory AutomorphicForm


noncomputable section

namespace LanglandsTunnell.CubicInduction

theorem CubicInductionForm.isCubicInductionDataOn {K : Type} [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (D : CubicInductionForm K pins ψ μ)
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ v, IsBadPlace K μ v → v ∈ S) :
    IsCubicInductionDataOn K pins ψ μ S D.toData :=
  { automorphic := D.automorphic, central := D.central, centralChar_ideleClass := D.centralChar_ideleClass,
    cuspidalP21 := D.cuspidalP21, cuspidalP12 := D.cuspidalP12, whittaker_eq := D.whittaker_eq,
    whittaker_law := D.whittaker_law, expansion := D.expansion, whittakerLoc_law := D.whittakerLoc_law,
    factorizable := fun g T hT hg => D.factorizable g T (fun v hv => hT v (hS v hv)) hg,
    spherical := fun v hv => D.spherical v (fun hb => hv (hS v hb)),
    levelInvariant := fun v _ hram => D.levelInvariant v hram, multOne := D.multOne,
    moderateGrowth := D.moderateGrowth, kFinite := D.kFinite, iotaMoments := D.iotaMoments,
    whittakerHalfPlane := D.whittakerHalfPlane, dualWhittaker_eq := D.dualWhittaker_eq,
    dualWhittaker_law := D.dualWhittaker_law, dual_expansion := D.dual_expansion,
    dual_iotaMoments := D.dual_iotaMoments, dual_whittakerHalfPlane := D.dual_whittakerHalfPlane }

theorem IsCubicInductionDataOn.exists_cubicInductionForm_toData_eq {K : Type} [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] {pins : CarrierPins ℚ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {Y : CubicInductionData}
    (hY : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} Y)
    (hlevel : ∀ v, ¬ IsRamifiedIn K v →
      ∀ k ∈ congruenceK1 (𝓞 ℚ) ℚ v (inducedLevelAt K μ v), ∀ g, Y.whittakerLoc v (g * k) = Y.whittakerLoc v g) :
    ∃ D : CubicInductionForm K pins ψ μ, D.toData = Y :=
  ⟨{ form := Y.form, whittaker := Y.whittaker, whittakerLoc := Y.whittakerLoc,
     whittakerArch := Y.whittakerArch, centralChar := Y.centralChar, dualWhittaker := Y.dualWhittaker,
     automorphic := hY.automorphic, central := hY.central, centralChar_ideleClass := hY.centralChar_ideleClass,
     cuspidalP21 := hY.cuspidalP21, cuspidalP12 := hY.cuspidalP12, whittaker_eq := hY.whittaker_eq,
     whittaker_law := hY.whittaker_law, expansion := hY.expansion, whittakerLoc_law := hY.whittakerLoc_law,
     factorizable := fun g T hT hg => hY.factorizable g T (fun v hv => hT v hv) hg,
     spherical := fun v hv => hY.spherical v hv, levelInvariant := hlevel, multOne := hY.multOne,
     moderateGrowth := hY.moderateGrowth, kFinite := hY.kFinite, iotaMoments := hY.iotaMoments,
     whittakerHalfPlane := hY.whittakerHalfPlane, dualWhittaker_eq := hY.dualWhittaker_eq,
     dualWhittaker_law := hY.dualWhittaker_law, dual_expansion := hY.dual_expansion,
     dual_iotaMoments := hY.dual_iotaMoments, dual_whittakerHalfPlane := hY.dual_whittakerHalfPlane }, rfl⟩

theorem exists_isCubicInductionDataOn_productionPinsOf_of_exists_form_ne_zero
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (h : ∃ Φ : CubicInductionForm K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ, Φ.form ≠ 0) :
    ∃ X : CubicInductionData,
      IsCubicInductionDataOn K (productionPinsOf ℚ D U gen (AdelicBox.adelicBox ℚ)) ψ μ {v | IsBadPlace K μ v} X ∧
        X.form ≠ 0 := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨Φ.toData, Φ.isCubicInductionDataOn _ (fun _ hv => hv), hΦ⟩

end LanglandsTunnell.CubicInduction
end
