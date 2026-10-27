import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.Fourier.Scaling.Part2
open scoped FourierTransform
open MeasureTheory


namespace Real

/--
[Scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Fourier/Scaling.lean)
-/
@[path]
lemma fourier_comp_mul_left
-- given
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a : ℝ}
  (ha : a ≠ 0)
  (f : ℝ → E)
  (y : ℝ) :
-- imply
  FourierTransform.fourier (fun x => f (a * x)) y =
    (|a|⁻¹ : ℝ) • FourierTransform.fourier f (y / a) := by
-- proof
  simp only [Real.fourier_real_eq]
  let g : ℝ → E := fun v => (𝐞 (-(v * (y / a)))) • f v
  have hg : ∀ v, g (a * v) = (𝐞 (-(v * y))) • f (a * v) := by
    intro v
    simp only [g]
    congr 1
    congr 1
    field_simp
  simp_rw [← hg]
  rw [Measure.integral_comp_mul_left g a, abs_inv]

end Real

-- created on 2026-10-10
-- updated on 2026-10-26
