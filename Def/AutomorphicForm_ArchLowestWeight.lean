import Mathlib
import Def.AutomorphicForm_ViaCompactCuspNotion

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped Manifold

noncomputable section

namespace AutomorphicForm

def IsArchLowestWeightAt {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (hw : w.IsReal) (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∃ σ : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
    (((z.im : ℝ) : ℂ) ^ σ) * φ (g * adelicArchGLInclAt F w
      (Matrix.GeneralLinearGroup.map
        ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom)
        (iwasawaSectionGL z)))

end AutomorphicForm

end
