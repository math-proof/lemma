import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.FourierAnalysis
open MeasureTheory Complex Real FourierAnalysis
open scoped FourierTransform SchwartzMap


namespace FourierAnalysis

/--
[fourier_schwartz_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma fourier_schwartz_equiv
-- imply
  ∃ (Φ : SchwartzSpace ≃L[ℂ] SchwartzSpace), ∀ f : SchwartzSpace, (Φ f : ℝ → ℂ) = 𝓕 (f : ℝ → ℂ) :=
-- proof
  ⟨FourierTransform.fourierCLE ℂ SchwartzSpace, fun f => by
    simp [FourierTransform.fourierCLE]
    rfl⟩

end FourierAnalysis

namespace FourierAnalysis

/--
[real_inner_eq_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma real_inner_eq_mul
  {x y : ℝ} :
-- imply
  @inner ℝ ℝ _ x y = x * y := by
-- proof
  simp [inner, mul_comm]

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_transform_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma fourier_transform_scaling
  {f : ℝ → ℂ}
  {a : ℝ}
  {y : ℝ}
-- given
  (ha : 0 < a) :
-- imply
  𝓕 (fun x => f (a * x)) y = (a : ℂ)⁻¹ • 𝓕 f (y / a) := by
-- proof
  simp only [Real.fourier_eq, real_inner_eq_mul]
  have ha' : a ≠ 0 := ne_of_gt ha
  let g : ℝ → ℂ := fun v => (𝐞 (-(v * (y / a)))) • f v
  have hg : ∀ v, g (a * v) = (𝐞 (-(v * y))) • f (a * v) := by
    intro v; simp only [g]; congr 1; congr 1; field_simp
  simp_rw [← hg]
  rw [Measure.integral_comp_mul_left g a, abs_of_pos (inv_pos.mpr ha)]
  change (a⁻¹ : ℝ) • ∫ v, g v = ((↑a : ℂ)⁻¹) • ∫ v, (𝐞 (-(v * (y / a)))) • f v
  simp only [g, Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]

end FourierAnalysis

namespace FourierAnalysis

/--
[fderiv_fourier_eq_fourier_neg_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma fderiv_fourier_eq_fourier_neg_smul
  {f : SchwartzSpace} :
-- imply
  SchwartzMap.fderivCLM ℂ ℝ ℂ (𝓕 f) = 𝓕 (-(2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) f) :=
-- proof
  SchwartzMap.fderivCLM_fourier_eq ℂ f

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_fderiv_eq_smul_fourier](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma fourier_fderiv_eq_smul_fourier
  {f : SchwartzSpace} :
-- imply
  𝓕 (SchwartzMap.fderivCLM ℂ ℝ ℂ f) = (2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) (𝓕 f) :=
-- proof
  SchwartzMap.fourier_fderivCLM_eq ℂ f

end FourierAnalysis

namespace FourierAnalysis

/--
[fourier_fderiv_interchange](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma fourier_fderiv_interchange
  {f : SchwartzSpace} :
-- imply
  (SchwartzMap.fderivCLM ℂ ℝ ℂ (𝓕 f) = 𝓕 (-(2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) f)) ∧ (𝓕 (SchwartzMap.fderivCLM ℂ ℝ ℂ f) = (2 * ↑π * Complex.I) • SchwartzMap.smulRightCLM ℂ ℂ (innerSL ℝ) (𝓕 f)) :=
-- proof
  ⟨fderiv_fourier_eq_fourier_neg_smul f, fourier_fderiv_eq_smul_fourier f⟩

end FourierAnalysis

namespace FourierAnalysis

/--
[poisson_summation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma poisson_summation
  {f : SchwartzSpace} :
-- imply
  ∑' n : ℤ, f n = ∑' n : ℤ, (𝓕 (⇑f)) n := by
-- proof
  have h := SchwartzMap.tsum_eq_tsum_fourier f 0
  simp only [zero_add] at h
  rw [h]
  congr 1
  ext n
  simp only [QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one]
  rfl

end FourierAnalysis

namespace FourierAnalysis

/--
[euler_reflection_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/FourierAnalysis.lean)
-/
@[path]
lemma euler_reflection_formula
  {s : ℂ} :
-- imply
  Complex.Gamma s * Complex.Gamma (1 - s) = ↑Real.pi / Complex.sin (↑Real.pi * s) :=
-- proof
  Complex.Gamma_mul_Gamma_one_sub s

end FourierAnalysis


-- created on 2026-10-23
