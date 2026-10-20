import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Fourier.WienerTauberian
open MeasureTheory
open scoped Convolution FourierTransform
open MeasureTheory Complex
open scoped FourierTransform
open MathlibExt.Analysis.Fourier.WienerWanted


/--
[wiener_tauberian_L1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/WienerTauberian.lean)
-/
@[path]
private lemma wiener_tauberian_L1_eq
  {f : ℝ → ℂ}
-- given
  (hf : Integrable f volume)
  (hF : ∀ w : ℝ, 𝓕 f w ≠ 0) :
-- imply
  ∀ (g : ℝ → ℂ), Integrable g volume → ∀ ε > 0,
    ∃ (s : Finset ℝ) (c : ℝ → ℂ),
    Integrable (fun x => g x - ∑ t ∈ s, c t * f (x - t)) volume ∧
    ∫ x, ‖g x - ∑ t ∈ s, c t * f (x - t)‖ < ε := by
-- proof
  apply MathlibExt.Analysis.Fourier.WienerWanted.wiener_tauberian_L1 f hf hF


-- created on 2026-10-20
