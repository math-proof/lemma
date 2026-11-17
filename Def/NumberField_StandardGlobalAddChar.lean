module

public import Def.NumberField_StandardGlobalAddCharRat
public import Structure.NumberField_StandardGlobalAddChar

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.InfinitePlace PadicInt

noncomputable section

namespace NumberField.StandardAddChar

variable (F : Type) [Field F] [NumberField F]

namespace AdelicTraceData

variable {F}
variable (T : AdelicTraceData F)

def adelicTrace : AdeleRing (𝓞 F) F →+ AdeleRing (𝓞 ℚ) ℚ :=
  AddMonoidHom.prodMap T.traceInf T.traceFin

def psiK : AddChar (AdeleRing (𝓞 F) F) ℂ :=
  psiQ.compAddMonoidHom T.adelicTrace

end AdelicTraceData

end NumberField.StandardAddChar

end

end
