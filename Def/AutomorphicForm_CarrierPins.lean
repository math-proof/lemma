module

public import Instance.NumberField_AdelicHaar
public import Def.Measure_AdelicHaar
public import Def.AutomorphicForm_AdelicLsXi
public import Structure.AutomorphicForm_CarrierPins

@[expose] public section

open IsDedekindDomain NumberField Measure.AdelicHaar MeasureTheory Measure

noncomputable section

namespace AutomorphicForm


def productionPinsOf (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    CarrierPins F where
  mS := glBorel (Fin 2) (𝓞 F) F
  μ := adelicGLHaar (Fin 2) (𝓞 F) F
  D := D
  Z := ⊤
  U := U
  gen := gen
  nS := adeleBorel (𝓞 F) F
  ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B

end AutomorphicForm

end

end
