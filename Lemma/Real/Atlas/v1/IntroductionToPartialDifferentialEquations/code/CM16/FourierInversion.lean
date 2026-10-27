import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierInversion
open MeasureTheory Complex Finset FourierAnalysis
open scoped FourierTransform RealInnerProductSpace


namespace FourierAnalysis

/--
[fourier_inversion_forwardND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierInversion.lean)
-/
@[path]
lemma fourier_inversion_forwardND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {x : Fin n → ℝ}
-- given
  (hf_cont : Continuous f)
  (hf : Integrable f)
  (hf_hat : Integrable (fourierTransformND n f)) :
-- imply
  inverseFourierTransformND n (fourierTransformND n f) x = f x :=
-- proof
  fourier_inversionND n f hf hf_hat hf_cont x

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inversion_reverseND](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierInversion.lean)
-/
@[path]
lemma fourier_inversion_reverseND
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {x : Fin n → ℝ}
-- given
  (hf_cont : Continuous f)
  (hf : Integrable f)
  (hf_check : Integrable (inverseFourierTransformND n f)) :
-- imply
  fourierTransformND n (inverseFourierTransformND n f) x = f x := by
-- proof
  let g : EuclideanSpace ℝ (Fin n) → ℂ := f ∘ @WithLp.ofLp 2 (Fin n → ℝ)
  have hg_int : Integrable g :=
    ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding).mpr hf
  have hg_cont : Continuous g := hf_cont.comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  let h : EuclideanSpace ℝ (Fin n) → ℂ := fun y => g (-y)
  have hh_int : Integrable h := hg_int.comp_neg
  have hh_cont : Continuous h := hg_cont.comp continuous_neg
  have h_fg : 𝓕 h = 𝓕⁻ g := (Real.fourierInv_eq_fourier_comp_neg g).symm
  have hFh_int : Integrable (𝓕 h) := by
    rw [h_fg]
    have h_eq : inverseFourierTransformND n f = (𝓕⁻ g) ∘ (WithLp.toLp 2) :=
      funext (fun ξ => inverseFourierTransformND_eq_fourierInv_bridge n f ξ)
    rw [h_eq] at hf_check
    exact ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding).mp hf_check
  have h_inv : ∀ v : EuclideanSpace ℝ (Fin n), 𝓕⁻ (𝓕 h) v = h v :=
    fun v => hh_int.fourierInv_fourier_eq hFh_int hh_cont.continuousAt
  rw [h_fg] at h_inv
  have h1 := h_inv (-(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)))
  change 𝓕⁻ (𝓕⁻ g) (-WithLp.toLp 2 x) = g (- -WithLp.toLp 2 x) at h1
  rw [neg_neg] at h1
  rw [Real.fourierInv_eq_fourier_neg (𝓕⁻ g) (-WithLp.toLp 2 x)] at h1
  simp only [neg_neg] at h1
  rw [fourierTransformND_eq_fourier_bridge]
  have h_comp : (inverseFourierTransformND n f) ∘ @WithLp.ofLp 2 (Fin n → ℝ) = 𝓕⁻ g := by
    funext ξ
    show inverseFourierTransformND n f (WithLp.ofLp ξ) = 𝓕⁻ g ξ
    rw [inverseFourierTransformND_eq_fourierInv_bridge]
  rwa [h_comp]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_inversion_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/FourierInversion.lean)
-/
@[path]
lemma fourier_inversion_theorem
  {n : ℕ}
  {f : (Fin n → ℝ) → ℂ}
  {x : Fin n → ℝ}
-- given
  (hf_cont : Continuous f)
  (hf : Integrable f)
  (hf_hat : Integrable (fourierTransformND n f))
  (hf_check : Integrable (inverseFourierTransformND n f)) :
-- imply
  inverseFourierTransformND n (fourierTransformND n f) x = f x ∧ fourierTransformND n (inverseFourierTransformND n f) x = f x :=
-- proof
  ⟨fourier_inversion_forwardND n f hf_cont hf hf_hat x,
    fourier_inversion_reverseND n f hf_cont hf hf_check x⟩

end FourierAnalysis


-- created on 2026-10-23
