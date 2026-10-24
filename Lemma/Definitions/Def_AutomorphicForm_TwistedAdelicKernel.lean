import Lemma.Definitions.Def_AutomorphicForm_AdelicKernel

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

theorem twistedAdelicKernel_id {M : Type*} [AddCommMonoid M]
    (f : AdelicGL2 (𝓞 F) F → M) (x y : AdelicGL2 (𝓞 F) F) :
    twistedAdelicKernel F (MonoidHom.id _) f x y = adelicKernel F f x y :=
  rfl

theorem twistedAdelicKernel_one {M : Type*} [AddCommMonoid M]
    (f : AdelicGL2 (𝓞 F) F → M) (x y y' : AdelicGL2 (𝓞 F) F) :
    twistedAdelicKernel F 1 f x y = twistedAdelicKernel F 1 f x y' :=
  rfl

end AutomorphicForm
