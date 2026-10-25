import Def.AutomorphicForm_AdelicKernel

set_option autoImplicit false

open scoped NumberField

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def twistedAdelicKernel {M : Type*} [AddCommMonoid M]
    (σA : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F)
    (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) : M :=
  ∑ᶠ γ : Matrix.GeneralLinearGroup (Fin 2) F,
    f (x⁻¹ * globalPoints (𝓞 F) F γ * σA y)

end AutomorphicForm

end
