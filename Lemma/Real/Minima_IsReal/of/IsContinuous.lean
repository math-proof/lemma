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
  ∃ m : ℝ, IsMinOn f (Icc a b) m := by
-- proof
  obtain ⟨m, _, hm⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hf
  apply Exists.intro m hm


-- created on 2026-10-07
