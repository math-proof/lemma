import Mathlib
import sympy.Basic


@[path]
private lemma main
  {f g : ℝ → ℝ}
-- given
  (hf : MeasureTheory.Integrable f)
  (hg : MeasureTheory.Integrable g)
  (h : ∀ x, f x < g x) :
-- imply
  ∫ x, f x < ∫ x, g x := by
-- proof
  have key : ∫ x, (g x - f x) = (∫ x, g x) - (∫ x, f x) :=
    MeasureTheory.integral_sub hg hf
  have hpos : 0 < ∫ x, (g x - f x) := by
    apply (MeasureTheory.integral_pos_iff_support_of_nonneg
      (fun x => sub_nonneg.mpr (h x).le) (hg.sub hf)).mpr
    have hsupport : Function.support (fun x => g x - f x) = Set.univ := by
      ext x
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact sub_ne_zero.mpr (ne_of_gt (h x))
    rw [hsupport, Real.volume_univ]
    exact ENNReal.zero_lt_top
  linarith [key, hpos]


-- created on 2026-10-07
