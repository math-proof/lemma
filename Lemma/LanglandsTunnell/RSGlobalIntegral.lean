import Lemma.LanglandsTunnell.CubicInduction_Structure
import Lemma.AutomorphicForm.SmoothingKernel

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.RankinSelberg

open LanglandsTunnell.CubicInduction AutomorphicForm

-- iotaGL_transposeInvN extracted to Lemma.Fin.IotaGL_TransposeInvN_Fin2.eq.TransposeInv3_IotaGL

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

def rsGlobalIntegral (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : ℂ :=
  ∫ g in D, φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)
    ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)

theorem rsGlobalIntegral_def (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    rsGlobalIntegral D s φ Θ =
      ∫ g in D, φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := rfl

@[simp] theorem rsGlobalIntegral_zero_left (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : rsGlobalIntegral D s 0 Θ = 0 := by
  simp [rsGlobalIntegral]

end LanglandsTunnell.RankinSelberg

end
