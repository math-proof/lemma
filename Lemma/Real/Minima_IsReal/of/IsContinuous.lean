import Mathlib
import Initialize.Tactic.Attr.Basic
open Set


@[path]
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


-- created on 2020-06-16
