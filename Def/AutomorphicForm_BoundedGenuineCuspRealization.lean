import Lemma.AutomorphicForm.ProductionPinsGeneral
import Def.AutomorphicForm_WhittakerCoefficient
import Lemma.NumberField.AdelicTraceFin

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm.WindowedSiegel

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsBoundedOnSiegelWindows (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c → 0 < d₁ →
    ∃ C : ℝ, ∀ g ∈ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂), ‖φ g‖ ≤ C

def IsBoundedGenuineFn (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  Continuous φ ∧
    IsBoundedOnSiegelWindows F φ ∧
    (∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F pins ψ φ α g) ∧
    ∀ g : AdelicGL2 (𝓞 F) F, Summable (fun α : F => whittakerCoefficient F pins ψ φ α g)

def IsBoundedGenuineCuspRealizationAt (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Φ) : Prop :=
  IsBoundedGenuineFn F pins ψ R.toFun

def IsBoundedGenuineCuspRealizable (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ R : SmoothCuspRealizationAt F pins Φ, IsBoundedGenuineCuspRealizationAt F pins ψ Φ R

def IsArithBoundedGenuineCuspRealizable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  IsBoundedGenuineCuspRealizable F pins ψ Φ.toRawCentral

def IsArithBoundedGenuineCuspRealizableVia (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {R : Type*} [CommRing R] (ι : R →+* ℂ)
    (Φ : HeckeEigensystem F R) : Prop :=
  IsArithBoundedGenuineCuspRealizable F pins ψ (Φ.map ι)

def boundedGenuineCuspNotionOf
    (pins : ∀ (F : Type) [Field F] [NumberField F], CarrierPins F) :
    CuspidalityNotion ℂ where
  IsCusp := fun F _i1 _i2 Φ =>
    @IsArithBoundedGenuineCuspRealizable F _i1 _i2 (pins F)
      (@NumberField.StandardAddChar.stdAddChar F _i1 _i2) Φ

end AutomorphicForm

end
