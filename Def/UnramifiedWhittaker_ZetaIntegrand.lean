import Lemma.AdelicDock.LocalEmbedding
import Def.NumberField_TateGlobalZeta
import Lemma.AutomorphicForm.HeckeEigenfunction
import Def.NumberField_IdeleBox

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Polynomial
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal
open AutomorphicForm AdelicDock

namespace UnramifiedWhittaker

def zetaIntegrand {F : Type} [Field F] [NumberField F] (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) : ℂ :=
  W (diagOne a) * ((χ a : ℂˣ) : ℂ) * ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)

end UnramifiedWhittaker

end
