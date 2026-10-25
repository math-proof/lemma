import Lemma.AutomorphicForm.CarrierPins
import Def.AutomorphicForm_ConstantTerm

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

section LsXiAt

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def LsXiMemberAt [MeasurableSpace (AdelicGL2 R K)] (μ : Measure (AdelicGL2 R K))
    (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) (D : Set (AdelicGL2 R K))
    (φ : AdelicGL2 R K → ℂ) : Prop :=
  @LsXiMember R K _ _ _ _ _ Z ξ ⟨μ⟩ D φ

end LsXiAt

variable (F : Type) [Field F] [NumberField F]

def IsAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  @LsXiMemberAt (𝓞 F) F _ _ _ _ _ pins.mS pins.μ pins.Z ξ pins.D φ

def IsCuspAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsAutomorphicFnAt F pins ξ φ ∧ @IsCuspidalFn _ pins.nS _ _ pins.ν unipotentGL2 φ

end AutomorphicForm

end
