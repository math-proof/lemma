import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {p : ℝ}
-- given
  (h₀ : 0 < p)
  (h₁ : p < 1) :
-- imply
  Real.log (p / (1 - p)) = Real.log p - Real.log (1 - p) ∧ 0 < -Real.log p := by
-- proof
  constructor
  ·
    exact Real.log_div (ne_of_gt h₀) (ne_of_gt (sub_pos.mpr h₁))
  ·
    have hlog : Real.log p < 0 := Real.log_neg h₀ h₁
    linarith


-- created on 2023-10-06
-- updated on 2026-10-26
