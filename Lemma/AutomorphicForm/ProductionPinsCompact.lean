import Lemma.AutomorphicForm.ProductionPins
import Lemma.AutomorphicForm.SmoothAutomorphicFnAt
import Def.AutomorphicForm_ProductionPinsCompact

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


@[simp] theorem productionPinsCompact_mS :
    (productionPinsCompact F).mS = glBorel (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_μ :
    (productionPinsCompact F).μ = adelicGLHaar (Fin 2) (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_D :
    (productionPinsCompact F).D = centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2 := rfl

@[simp] theorem productionPinsCompact_Z :
    (productionPinsCompact F).Z = (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) := rfl

@[simp] theorem productionPinsCompact_U (N : Ideal (𝓞 F)) :
    (productionPinsCompact F).U N = levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := rfl

@[simp] theorem productionPinsCompact_gen (v : HeightOneSpectrum (𝓞 F)) :
    (productionPinsCompact F).gen v = heckeGen (𝓞 F) F v := rfl

@[simp] theorem productionPinsCompact_nS :
    (productionPinsCompact F).nS = adeleBorel (𝓞 F) F := rfl

@[simp] theorem productionPinsCompact_ν :
    (productionPinsCompact F).ν =
      @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) (adelicBox F) :=
  rfl

theorem productionPinsCompact_μ_eq_productionPins_μ :
    (productionPinsCompact F).μ = (productionPins F).μ := rfl

theorem productionPinsCompact_D_eq_productionPins_D :
    (productionPinsCompact F).D = (productionPins F).D := rfl

theorem productionPinsCompact_ν_eq_productionPins_ν :
    (productionPinsCompact F).ν = (productionPins F).ν := rfl

theorem glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U (N : Ideal (𝓞 F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (productionPinsCompact F).U N) :
    glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N :=
  hu.1

theorem glArch_eq_one_of_mem_productionPinsCompact_U (N : Ideal (𝓞 F))
    {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ (productionPinsCompact F).U N) :
    glArch (𝓞 F) F u = 1 :=
  hu.2

theorem productionPinsCompact_U_eq_productionPins_U_inf (N : Ideal (𝓞 F)) :
    (productionPinsCompact F).U N = (productionPins F).U N ⊓ finiteAdelicGL2Subgroup F := rfl

theorem productionPinsCompact_U_le_productionPins_U (N : Ideal (𝓞 F)) :
    (productionPinsCompact F).U N ≤ (productionPins F).U N := inf_le_left

theorem isHaarMeasure_productionPinsCompact_μ :
    @Measure.IsHaarMeasure _ _ _ (productionPinsCompact F).mS (productionPinsCompact F).μ :=
  isHaarMeasure_productionPins_μ F

theorem isProbabilityMeasure_productionPinsCompact_ν :
    @IsProbabilityMeasure _ (productionPinsCompact F).nS (productionPinsCompact F).ν :=
  isProbabilityMeasure_productionPins_ν F

theorem measurableSet_productionPinsCompact_D :
    @MeasurableSet _ (productionPinsCompact F).mS (productionPinsCompact F).D :=
  measurableSet_productionPins_D F

theorem productionPinsCompact_μ_D_pos_lt_top :
    (letI := (productionPinsCompact F).mS;
      0 < (productionPinsCompact F).μ (productionPinsCompact F).D ∧
        (productionPinsCompact F).μ (productionPinsCompact F).D < ⊤) :=
  productionPins_μ_D_pos_lt_top F

end AutomorphicForm

end
