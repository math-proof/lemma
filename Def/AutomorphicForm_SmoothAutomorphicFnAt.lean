import Def.AutomorphicForm_AutomorphicFnAt
import Instance.RepTheory_SmoothVectors
import Lemma.NumberField.AdelicLevel

open IsDedekindDomain NumberField MeasureTheory Matrix
open FLT.SmoothVectors
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def finiteAdelicGL2Subgroup : Subgroup (AdelicGL2 (𝓞 F) F) :=
  MonoidHom.ker (NumberField.AdelicLevel.glArch (𝓞 F) F)


def IsKfSmooth (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsSmoothVector (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)


def IsSmoothAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsAutomorphicFnAt F pins ξ φ ∧ IsKfSmooth F φ

def IsSmoothCuspAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsCuspAutomorphicFnAt F pins ξ φ ∧ IsKfSmooth F φ

end AutomorphicForm

end
