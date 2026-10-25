import Lemma.LanglandsTunnell.CubicInduction_Structure
import Def.UnramifiedWhittaker_HeckeRecursion

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

noncomputable section

namespace LanglandsTunnell.CubicInduction

section CellBump

variable (v : HeightOneSpectrum (𝓞 ℚ))

def IsCellBumpAt (ψv : AddChar (v.adicCompletion ℚ) ℂ) (𝔡 : Ideal (𝓞 ℚ)) (t₀ : GL (Fin 2) (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) : Prop :=
  IsGL3PsiWhittakerFn ψv W ∧
  (∀ x : GL (Fin 2) (v.adicCompletion ℚ),
    (¬ ∃ n ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
      ∃ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v 𝔡, x = n * t₀ * k) →
    W (iotaGL x) = 0) ∧
  (∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v 𝔡, W (iotaGL (t₀ * k)) = W (iotaGL t₀)) ∧
  W (iotaGL t₀) = 1

end CellBump

section Existence

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def IsNormalizedOffRamified (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (D : CubicInductionForm K pins ψ μ) : Prop :=
  D.form ≠ 0 ∧ ∀ v, ¬ IsRamifiedIn K v →
    LanglandsTunnell.TateLocal.addCharLevel (psiLoc ψ v) = 0 →
      D.whittakerLoc v 1 = 1 ∧ HasSphericalTorusValuesAt (inducedCoeff K μ) v (D.whittakerLoc v)


def HasCellBumpsOn (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (π : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ) (hπ : ∀ v, π v ≠ 0)
    (m₀ : HeightOneSpectrum (𝓞 ℚ) → ℤ) : Prop :=
  (∀ v ∈ T, IsRamifiedIn K v) →
  (∀ v ∈ T, ∀ r : v.adicCompletionIntegers ℚ,
    psiLoc ψ v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) →
  (∀ v ∈ T, psiLoc ψ v ≠ 1) → (∀ v ∈ T, Valued.v (π v) = WithZero.exp (-1 : ℤ)) → (∀ v ∈ T, 0 ≤ m₀ v) →
  ∃ (D : CubicInductionForm K pins ψ μ) (𝔡 : HeightOneSpectrum (𝓞 ℚ) → Ideal (𝓞 ℚ)),
    IsNormalizedOffRamified K pins ψ μ D ∧ (∀ v ∈ T, 𝔡 v ≠ ⊥) ∧
    ∀ v ∈ T, IsCellBumpAt v (psiLoc ψ v) (𝔡 v) (UnramifiedWhittaker.diagZ (π v) (hπ v) (m₀ v)) (D.whittakerLoc v)

end Existence

end LanglandsTunnell.CubicInduction

end
