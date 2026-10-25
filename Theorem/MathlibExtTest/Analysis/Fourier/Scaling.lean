/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Fourier/Scaling.lean -/


import Lemma.Real.Fourier_UFnMul.eq.SMulFourier.of.Ne_0
import Lemma.Real.Fourier_UFnMul.eq.SMulFourier.of.Gt_0
import Lemma.Real.Fourier_Coe_UFnMul.eq.SMulFourier.of.Gt_0
open scoped FourierTransform


example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → E) (y : ℝ) : 𝓕 (fun x => f (1 * x)) y =
      (|(1 : ℝ)|⁻¹ : ℝ) • 𝓕 f (y / 1) := by
  exact Real.fourier_comp_mul_left f (a := 1) one_ne_zero y

example (f : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x => f (2 * x)) y = ((2 : ℝ)⁻¹ : ℂ) • 𝓕 f (y / 2) := by
  simpa using Real.fourier_comp_mul_left_of_pos f (a := 2) (by norm_num) y

example (f : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x => f ((-2) * x)) y = ((2 : ℝ)⁻¹ : ℂ) • 𝓕 f (y / (-2)) := by
  simpa using Real.fourier_comp_mul_left f (a := -2) (by norm_num : (-2 : ℝ) ≠ 0) y

example (f : SchwartzMap ℝ ℂ) (y : ℝ) :
    𝓕 (fun x => ⇑f (2 * x)) y = ((2 : ℝ)⁻¹ : ℂ) • 𝓕 ⇑f (y / 2) := by
  simpa using SchwartzMap.fourier_coe_comp_mul_left_of_pos f (a := 2) (by norm_num) y

