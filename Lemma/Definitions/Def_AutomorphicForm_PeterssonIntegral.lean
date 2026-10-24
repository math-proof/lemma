import Lemma.Definitions.Def_NumberField_TateGlobalZeta

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicHaar

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def peterssonIntegral (s : ℝ) (S : Set (AdelicGL2 (𝓞 F) F)) (x y : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  letI := glBorel (Fin 2) (𝓞 F) F
  ∫ g in S,
    x g * (starRingEnd ℂ) (y g) *
      ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-s) : ℝ) : ℂ)
    ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

end AutomorphicForm

end
