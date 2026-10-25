import Mathlib
import Def.AutomorphicForm_ViaCompactCuspNotion
import Lemma.AutomorphicForm.ProductionPinsGeneral

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsInTranslateSpanOn (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
      ∫⁻ y in D, (‖φ' y - ∑ h ∈ s, l h * φ (y * h)‖₊ : ℝ≥0∞) ^ 2
        ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε

variable {F}


open TranslateSpanOccurrence

variable (F)

def ArchOccursInClassOf (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) : Prop :=
  ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
    ∃ R' : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral,
      IsGenuineCuspRealizationAt F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Θ'.toRawCentral R' ∧
      P R'.toFun

variable {F}


variable (F)

def ArchOccursInSpanOf (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) : Prop :=
  ∃ Θ' : HeckeEigensystem F ℂ, Θ'.AgreesAwayFromFinite Θ ∧
    ∃ R' : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral,
      IsGenuineCuspRealizationAt F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Θ'.toRawCentral R' ∧
      IsInTranslateSpanOn F D R.toFun R'.toFun ∧ P R'.toFun

end AutomorphicForm

end
