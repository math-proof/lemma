import Lemma.Real.EqLim.is.All_Any_All_LtAbsSub
import sympy.concrete.quantifier
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Set Real


@[path]
private lemma main
  {f : ℝ → ℝ}
  {x₀ a : ℝ}
-- given
  (h : lim [x → x₀] f x = a) :
-- imply
  ∃ M > 0, ∃ δ > 0, ∀ x | |x - x₀| ∈ Ioo 0 δ, |f x| ≤ M := by
-- proof
  obtain ⟨δ, hδ, H⟩ := All_Any_All_LtAbsSub.of.EqLim.εδ h 1 one_pos
  refine ⟨|a| + 1, by positivity, δ, hδ, fun x hx => ?_⟩
  have hε : |f x - a| < 1 := H x hx
  have : |f x| ≤ |f x - a| + |a| := by
    simpa [sub_eq_add_neg] using abs_add_le (f x - a) a
  linarith


-- created on 2026-10-11
-- updated on 2026-10-12
