import Mathlib
import sympy.Basic
open Set



@[main]
private lemma main
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hab : a ≤ b)
  (hf : ContinuousOn f (Icc a b)) :
-- imply
  ∃ M : ℝ, IsMaxOn f (Icc a b) M := by
-- proof
  obtain ⟨M, _, hM⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf
  apply Exists.intro M hM


-- created on 2026-10-07
