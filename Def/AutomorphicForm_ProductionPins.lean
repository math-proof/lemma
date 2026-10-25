import Def.NumberField_AdelicBox
import Lemma.NumberField.SiegelVolume

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.SiegelVolume

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def productionPins : CarrierPins F :=
  productionPinsOf F
    (centreCutSiegelSet F (1/2 : ℝ) 1 (1/2) 2)
    (fun N => levelOne (𝓞 F) F N)
    (fun v => heckeGen (𝓞 F) F v)
    (adelicBox F)

end AutomorphicForm

end
