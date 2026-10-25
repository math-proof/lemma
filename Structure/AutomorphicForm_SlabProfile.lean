import Def.AutomorphicForm_BorelSubgroup
import Def.AutomorphicForm_WeylIntertwining
import Def.NumberField_AdelicHeight
import Def.NumberField_TateGlobalZeta

open MeasureTheory NumberField
open NumberField.AdelicHaar


noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

structure IsSlabProfile (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop where
  measurable : Measurable φ
  unipotent_mul : ∀ (x : AdeleRing (𝓞 F) F) (g : AdelicGL2 (𝓞 F) F),
    φ (unipotentGL2 x * g) = φ g
  borel_mul : ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
    φ (globalPoints (𝓞 F) F γ * g) = φ g
  central_transform : ∀ (z : Z) (g : AdelicGL2 (𝓞 F) F),
    φ (centralScalar (𝓞 F) F (z : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * φ g
  bounded_on_slab : ∀ d₁ d₂ : ℝ, 0 < d₁ → ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
    NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂ →
      ‖φ g‖ ≤ C
  height_band : ∃ a b : ℝ, 0 < a ∧ ∀ g : AdelicGL2 (𝓞 F) F,
    φ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b


variable {F}


end AutomorphicForm

end
