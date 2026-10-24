import Lemma.Definitions.Def_AutomorphicForm_BorelSubgroup
import Lemma.Definitions.Def_AutomorphicForm_WeylIntertwining
import Lemma.Definitions.Def_NumberField_AdelicHeight
import Lemma.Definitions.Def_NumberField_TateGlobalZeta

open MeasureTheory NumberField
open NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel

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
