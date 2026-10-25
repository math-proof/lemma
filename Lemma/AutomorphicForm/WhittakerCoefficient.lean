import Lemma.AutomorphicForm.CarrierPins
import Def.AutomorphicForm_ConstantTerm
import Def.AutomorphicForm_WhittakerCoefficient
import Structure.AutomorphicForm_WhittakerCoefficient

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]


theorem isPrincipalInvariantAddChar_one :
    IsPrincipalInvariantAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun _ => rfl

theorem not_isGlobalAddChar_one :
    ¬ IsGlobalAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun h => h.nontrivial rfl


@[simp] theorem whittakerCoefficient_zero (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) α g = 0 := by
  letI := pins.nS
  simp only [whittakerCoefficient, zero_mul, integral_zero]

theorem whittakerCoefficient_zero_eq_constantTerm (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g
      = @constantTerm _ pins.nS _ _ pins.ν unipotentGL2 φ g := by
  letI := pins.nS
  simp only [whittakerCoefficient, map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one,
    mul_one]
  rfl

end AutomorphicForm

end
