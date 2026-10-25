import Structure.AutomorphicForm_IsotypicCuspSpace
import Def.AutomorphicForm_FactorizableTestFn

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

namespace CuspidalConstituent

variable (F : Type) [Field F] [NumberField F]

def rightTranslate (g : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  fun x => φ (x * g)


def cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  Submodule.span ℂ
    {φ | (∀ g : AdelicGL2 (𝓞 F) F, IsSmoothCuspAutomorphicFnAt F pins ξ (rightTranslate F g φ)) ∧
      Continuous φ ∧ ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys}


structure IsCuspSubrep (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) : Prop where
  le : V ≤ cuspKFiniteSubmodule F pins ξ
  rightTranslate_fin_mem : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ φ ∈ V, rightTranslate F g φ ∈ V
  rightTranslate_arch_mem : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
    ∀ φ ∈ V, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ V
  rightConv_mem : ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F),
    IsFactorizableTestFn F f → IsArchBiFinite F tys f → ∀ φ ∈ V, rightConv F φ f ∈ V


end CuspidalConstituent

end AutomorphicForm

end
