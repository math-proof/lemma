module

public import Def.NumberField_AdelicLevel

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))

end AutomorphicForm

end
