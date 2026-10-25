import Instance.NumberField_AdelicHaar

open NumberField

namespace AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def rightConv (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun g =>
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
     ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))

end AutomorphicForm
