import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Lemma.Definitions.Def_AutomorphicForm_SmoothingKernel

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.RankinSelberg

open LanglandsTunnell.CubicInduction AutomorphicForm

theorem iotaGL_transposeInvN {A : Type*} [CommRing A] (g : GL (Fin 2) A) :
    iotaGL (transposeInvN (Fin 2) g) = transposeInv3 (iotaGL g) := by
  refine Units.ext ?_
  change embedMat2 _ = (((iotaGL g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
  rw [← map_inv, coe_iotaGL, coe_transposeInvN]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

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
