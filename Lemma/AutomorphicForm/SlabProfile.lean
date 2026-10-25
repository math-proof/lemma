import Lemma.AutomorphicForm.BorelSubgroup
import Lemma.AutomorphicForm.WeylIntertwining
import Def.NumberField_AdelicHeight
import Lemma.NumberField.TateGlobalZeta
import Structure.AutomorphicForm_SlabProfile

open MeasureTheory NumberField
open NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


def pseudoEisenstein (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ :=
  fun g => φ g + ∑' β : F, φ (adelicWeyl (𝓞 F) F
    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g)

variable {F}

theorem pseudoEisenstein_apply (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    pseudoEisenstein F φ g = φ g + ∑' β : F, φ (adelicWeyl (𝓞 F) F
      * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) :=
  rfl

theorem isSlabProfile_zero (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ) :
    IsSlabProfile F Z ξ (fun _ => (0 : ℂ)) where
  measurable := measurable_const
  unipotent_mul := fun _ _ => rfl
  borel_mul := fun _ _ _ => rfl
  central_transform := fun _ _ => by simp
  bounded_on_slab := fun _ _ _ => ⟨0, fun _ _ => by simp⟩
  height_band := ⟨1, 1, one_pos, fun _ h => absurd rfl h⟩

theorem pseudoEisenstein_zero :
    pseudoEisenstein F (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
  funext g
  simp [pseudoEisenstein]

end AutomorphicForm

end
